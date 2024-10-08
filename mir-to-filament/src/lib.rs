use core::panic;
use std::{collections::HashMap, io, path::PathBuf};

use bimap::BiMap;
pub use fil;
use fil::ir_passes as fil_ip;
use fil_ir::{AddCtx, Ctx, MutCtx};
use spade_mir::{codegen::Codegenable, types::Type, Entity, Operator, Statement, ValueName};

const NO_LOC: fil_utils::GPosIdx = fil_utils::GPosIdx::UNKNOWN;

#[derive(Default, Clone)]
pub(crate) struct FilamentSignature {
    pub(crate) event_args: HashMap<String, fil_ir::EventIdx>,
    pub(crate) ports: HashMap<String, fil_ir::PortIdx>,
    pub(crate) ports_ordered: Vec<fil_ir::PortIdx>,
}

impl FilamentSignature {
    pub(crate) fn from(comp: &fil_ir::Component) -> Self {
        if let Some(i) = &comp.src_info {
            println!("comp {}", i.name);
        }

        let mut event_args = HashMap::new();
        for event_arg_idx in &comp.event_args {
            let event = comp.get(*event_arg_idx);
            let name = comp
                .get(event.info)
                .as_event()
                .expect("event arg info was not ::Event")
                .name
                .to_string();
            event_args.insert(name, *event_arg_idx);
        }

        let mut ports = HashMap::new();
        let mut ports_ordered = Vec::new();
        for (port_idx, port) in comp.ports.iter() {
            if let Some(name) = comp
                .get(port.info)
                .as_port()
                .map(|info| info.name.to_string())
            {
                ports.insert(name, port_idx);
            }
            ports_ordered.push(port_idx);
            println!("port: {}", comp.get(port.info).as_port().unwrap().name);
        }

        Self {
            event_args,
            ports,
            ports_ordered,
        }
    }
}

pub(crate) struct FilamentComponentBuilder<'c, 's> {
    comp: &'c mut fil_ir::Component,
    comp_idx: fil_ir::CompIdx,
    comp_ctx: &'s FilamentGlobalContext,
    name_gen: usize,
}

impl<'c, 's> FilamentComponentBuilder<'c, 's> {
    pub(crate) fn new_in<S: AsRef<str>>(
        ctx: &'c mut fil_ir::Context,
        comp_ctx: &'s FilamentGlobalContext,
        name: S,
    ) -> Self {
        let comp_idx = ctx.comp(fil_ir::CompType::Source /* should be Generated? but can't figure out the tool thing then */, fil_ast::Attributes::default());
        let comp = ctx.get_mut(comp_idx);
        comp.src_info = Some(fil_ir::InterfaceSrc::new(name.as_ref().into(), None));

        Self {
            comp,
            comp_idx,
            comp_ctx,
            name_gen: 0,
        }
    }

    pub(crate) fn add_const(&mut self, value: u64) -> fil_ir::ExprIdx {
        self.add_expr(fil_ir::Expr::Concrete(value))
    }

    pub(crate) fn add_expr(&mut self, expr: fil_ir::Expr) -> fil_ir::ExprIdx {
        self.comp.add(expr)
    }

    pub(crate) fn add_event<S: AsRef<str>>(
        &mut self,
        name: S,
        delay: fil_ir::TimeSub,
    ) -> fil_ir::EventIdx {
        let name = name.as_ref().into();
        let interface_port_name = name; // idk what this is
        let info = self.comp.add(fil_ir::Info::event(
            name,
            NO_LOC,
            NO_LOC,
            Some((interface_port_name, NO_LOC)),
        ));
        let event_idx = self.comp.add(fil_ir::Event {
            delay,
            info,
            has_interface: true,
        });

        // there has to be a better way to do this
        self.comp.event_args = {
            let mut events = self.comp.event_args.to_vec();
            events.push(event_idx);
            events.into_boxed_slice()
        };

        self.interface().events.push(event_idx, name);
        self.interface()
            .interface_ports
            .push(event_idx, interface_port_name);
        event_idx
    }

    pub(crate) fn add_time(
        &mut self,
        event: fil_ir::EventIdx,
        offset: fil_ir::ExprIdx,
    ) -> fil_ir::TimeIdx {
        self.comp.add(fil_ir::Time { event, offset })
    }

    pub(crate) fn add_port<S: AsRef<str>>(
        &mut self,
        name: S,
        owner: fil_ir::PortOwner,
        width: fil_ir::ExprIdx,
        live: fil_ir::Liveness,
    ) -> fil_ir::PortIdx {
        let name = name.as_ref().into();
        let info = self.comp.add(fil_ir::Info::Port(fil_ir::info::Port {
            name,
            bind_loc: NO_LOC,
            width_loc: NO_LOC,
            live_loc: NO_LOC,
        }));
        let port = fil_ir::Port {
            owner,
            width,
            live,
            info,
        };
        let port_idx = self.comp.add(port);
        self.interface().ports.push(port_idx, name);
        port_idx
    }

    pub(crate) fn new_event_bind(
        &mut self,
        start: fil_ir::EventIdx,
        delay: fil_ir::ExprIdx,
    ) -> fil_ir::EventBind {
        let info = self.comp.add(fil_ir::Info::event_bind(NO_LOC, NO_LOC));
        fil_ir::EventBind::new(
            fil_ir::TimeSub::Unit(delay),
            self.add_time(start, delay),
            info,
            fil_ir::Foreign::new(start, self.idx()),
        )
    }

    pub(crate) fn port_on_inv<S: AsRef<str>>(
        &self,
        invocation: fil_ir::InvIdx,
        name: S,
    ) -> fil_ir::PortIdx {
        self.comp
            .get(invocation)
            .ports
            .iter()
            .cloned()
            .find(|port_idx| {
                let port = self.comp.get(*port_idx);
                let info = self.comp.get(port.info);
                info.as_port().expect("non-port info for port").name == name.as_ref()
            })
            .expect("invalid port for invocation")
    }

    pub(crate) fn comp_from_name<S: AsRef<str>>(&self, name: S) -> Option<fil_ir::CompIdx> {
        self.comp_ctx.comp_map.get_by_left(name.as_ref()).cloned()
    }

    pub(crate) fn sig_for(&self, comp: fil_ir::CompIdx) -> &FilamentSignature {
        self.comp_ctx.sig_map.get(comp)
    }

    pub(crate) fn instantiate<const N: usize>(
        &mut self,
        comp: fil_ir::CompIdx,
        args: [fil_ir::ExprIdx; N],
        lives: Vec<fil_ir::Range>,
        params: Vec<fil_ir::ParamIdx>,
    ) -> fil_ir::InstIdx {
        let name = self
            .name_gen(
                self.comp_ctx
                    .comp_map
                    .get_by_right(&comp)
                    .expect("unknown comp"),
            )
            .into();
        let info = self
            .comp
            .add(fil_ir::Info::instance(name, NO_LOC, NO_LOC, vec![]));
        let instance = self.comp.add(fil_ir::Instance {
            comp,
            args: Box::new(args),
            lives,
            params,
            info,
        });
        self.comp.cmds.push(fil_ir::Command::Instance(instance));
        instance
    }

    pub(crate) fn invoke<S: AsRef<str>>(
        &mut self,
        name: S,
        inst: fil_ir::InstIdx,
        events: Vec<fil_ir::EventBind>,
    ) -> fil_ir::InvIdx {
        let name = self.name_gen(name).into();
        let info = self
            .comp
            .add(fil_ir::Info::invoke(name, NO_LOC, NO_LOC, vec![]));
        let invocation = self.comp.add(fil_ir::Invoke {
            inst,
            events,
            ports: vec![],
            info,
        });
        self.comp.cmds.push(fil_ir::Command::Invoke(invocation));

        let ports = {
            let foreign_comp = self.comp.get(inst).comp;
            let mut ports = Vec::new();
            for port_idx in self
                .comp_ctx
                .sig_map
                .get(foreign_comp)
                .ports_ordered
                .iter()
                .cloned()
            {
                let comp_port = self.comp.get(port_idx);
                let base = fil_ir::Foreign::new(port_idx, foreign_comp);
                let name = self
                    .comp
                    .get(comp_port.info)
                    .as_port()
                    .expect("non-port info on port")
                    .name;
                let inv_port = self.add_port(
                    name,
                    fil_ir::PortOwner::inv_in(invocation, base),
                    comp_port.width, // pretty sure this copying over doesn't work since the
                    // liveliness would be different right?
                    comp_port.live.clone(),
                );
                ports.push(inv_port);
            }
            ports
        };
        self.comp.get_mut(invocation).ports.extend(ports);

        invocation
    }

    pub(crate) fn connect(&mut self, lhs: fil_ir::PortIdx, rhs: fil_ir::PortIdx) {
        let info = self.comp.add(fil_ir::Info::connect(NO_LOC, NO_LOC));
        let src = fil_ir::Access::port(rhs, self.comp);
        let dst = fil_ir::Access::port(lhs, self.comp);
        let connect = fil_ir::Connect { src, dst, info };
        self.comp.cmds.push(fil_ir::Command::Connect(connect));
    }

    pub(crate) fn idx(&self) -> fil_ir::CompIdx {
        self.comp_idx
    }

    pub(crate) fn comp(&mut self) -> &mut fil_ir::Component {
        self.comp
    }

    fn interface(&mut self) -> &mut fil_ir::InterfaceSrc {
        self.comp
            .src_info
            .as_mut()
            .expect("initialized in constructor")
    }

    fn name_gen<S: AsRef<str>>(&mut self, name: S) -> String {
        let id = self.name_gen;
        self.name_gen += 1;
        format!("{}_{}", name.as_ref(), id)
    }
}

macro_rules! build {
    ($builder:expr; const $value:expr) => {
        $builder.add_const($value)
    };
    ($builder:expr; event $event:ident:$delay:expr) => {
        $builder.add_event(stringify!($event), fil_ir::TimeSub::Unit($delay))
    };
    ($builder:expr; live [$start:ident + $start_off:expr, $end:ident + $end_off:expr]) => {{
        let start_time = $builder.add_time($start, $start_off);
        let end_time = $builder.add_time($end, $end_off);
        fil_ir::Liveness {
            idxs: vec![],
            lens: vec![],
            range: fil_ir::Range {
                start: start_time,
                end: end_time,
            },
        }
    }};
}

fn spade_type_to_fil_port<S: AsRef<str>>(
    builder: &mut FilamentComponentBuilder,
    name: S,
    ty: &Type,
    owner: fil_ir::PortOwner,
    live: fil_ir::Liveness,
) -> fil_ir::PortIdx {
    let width = builder.add_const(spade_type_width(ty));
    builder.add_port(name, owner, width, live)
}

fn spade_type_width(ty: &Type) -> u64 {
    let &[width] = ty.size().to_u64_digits().as_slice() else {
        // probaby breaks compound types for now
        panic!("could not convert type width into u64");
    };
    width
}

pub(crate) struct ComponentBuilderContext {
    start: fil_ir::EventIdx,
    instances: Vec<Option<fil_ir::InstIdx>>,
    ports: HashMap<ValueName, fil_ir::PortIdx>,
}

impl Default for ComponentBuilderContext {
    fn default() -> Self {
        Self {
            start: fil_ir::EventIdx::UNKNOWN,
            instances: Vec::default(),
            ports: HashMap::default(),
        }
    }
}

impl ComponentBuilderContext {
    pub(crate) fn port(&self, value_name: &ValueName) -> fil_ir::PortIdx {
        self.ports
            .get(value_name)
            .cloned()
            .unwrap_or_else(|| panic!("{:?} not bound to port yet", value_name))
    }

    pub(crate) fn bind(&mut self, value_name: ValueName, port: fil_ir::PortIdx) {
        self.ports.insert(value_name, port);
    }

    pub(crate) fn instance_at(&self, index: usize) -> fil_ir::InstIdx {
        self.instances[index].unwrap()
    }
}

fn build_signature(
    context: &mut ComponentBuilderContext,
    builder: &mut FilamentComponentBuilder,
    entity: &Entity,
) {
    let zero = build!(builder; const 0);
    let one = build!(builder; const 1);
    let ii = build!(builder; const 1); // MARK: spade only allows II=1
    let start_event = build!(builder; event S:ii);
    context.start = start_event;

    context.ports.extend(entity.inputs.iter().map(|input| {
        let live = build!(builder; live [start_event + zero, start_event + one]);
        let port = spade_type_to_fil_port(
            builder,
            format!("{}_i", input.name),
            &input.ty,
            fil_ir::PortOwner::sig_out(),
            live,
        );
        (input.val_name.clone(), port)
    }));

    let length = build!(builder; const entity.pipeline_latency.unwrap() as u64);
    let output_live = build!(builder; live [start_event + length, start_event + length]);
    context.ports.insert(
        entity.output.clone(),
        spade_type_to_fil_port(
            builder,
            "output",
            &entity.output_type,
            fil_ir::PortOwner::sig_in(),
            output_live,
        ),
    );
}

fn extract_instances(
    context: &mut ComponentBuilderContext,
    builder: &mut FilamentComponentBuilder,
    entity: &Entity,
) {
    for statement in &entity.statements {
        // println!("{:?}", statement);
        context.instances.push(match statement {
            Statement::Binding(binding) => match &binding.operator {
                Operator::Alias => {
                    let wire = builder.comp_from_name("Wire").unwrap();

                    let width = spade_type_width(&binding.ty);
                    let args = [build!(builder; const width)];
                    Some(builder.instantiate(wire, args, vec![], vec![]))
                }
                Operator::Nop => None,
                _ => todo!(),
            },
            Statement::Register(register) => {
                let reg = builder.comp_from_name("Register").unwrap();
                let width = spade_type_width(&register.ty);
                let args = [build!(builder; const width)];
                Some(builder.instantiate(reg, args, vec![], vec![]))
            }
            Statement::Constant(..)
            | Statement::Set { .. }
            | Statement::Assert(..)
            | Statement::WalTrace { .. } => None,
        });
    }
}

fn construct_invocations(
    context: &mut ComponentBuilderContext,
    builder: &mut FilamentComponentBuilder,
    entity: &Entity,
) -> u64 {
    let start = context.start;
    let mut now = 0;
    let zero = build!(builder; const 0);
    let one = build!(builder; const 1);
    for (i, statement) in entity.statements.iter().enumerate() {
        let now_time = build!(builder; const now);
        let soon_time = build!(builder; const now + 1);
        match statement {
            Statement::Binding(binding) => match &binding.operator {
                Operator::Alias => {
                    let rhs = context.port(&binding.operands[0]);
                    let wire = context.instance_at(i);
                    let event_bind = builder.new_event_bind(start, now_time);
                    let invocation = builder.invoke("spade_alias", wire, vec![event_bind]);
                    let live = build!(builder; live [start + now_time, start + soon_time]);
                    let width = builder.comp().get(rhs).width;

                    // I think base is the event on the invoked component it belongs to?
                    // TODO: make this a generalized method for getting a port of an invoke
                    // let wire_comp = builder.comp().get(wire).comp;
                    // let wire_sig = builder.sig_for(wire_comp);
                    // let foreign_out_port = wire_sig.ports.get("out").cloned().unwrap();
                    // let base = fil_ir::Foreign::new(foreign_out_port, wire_comp);
                    //
                    // let out_port = builder.add_port(
                    //     "out",
                    //     fil_ir::PortOwner::inv_out(invocation, base),
                    //     width,
                    //     live,
                    // );
                    // context.bind(binding.name.clone(), out_port);

                    // fil_ir::Command::Connect(fil_ir::Connect)
                }
                Operator::Nop => {}
                _ => todo!("{:?}", binding),
            },
            Statement::Register(register) => {
                now += 1;
            }
            Statement::Constant(..)
            | Statement::Set { .. }
            | Statement::Assert(..)
            | Statement::WalTrace { .. } => {}
        }
    }
    now
}

// Stores information about filament components needed to build filament IR when the actual context
// is mutably borrowed by a reference to the component being built.
pub(crate) struct FilamentGlobalContext {
    pub(crate) comp_map: BiMap<String, fil_ir::CompIdx>,
    pub(crate) sig_map:
        fil_ir::DenseIndexInfo<fil_ir::Component, FilamentSignature, fil_ir::CompIdx>,
}

fn build_fil_comp(ctx: &mut fil_ir::Context, comp_ctx: &FilamentGlobalContext, entity: &Entity) {
    let name = entity
        .name
        .to_string()
        .replace("::", "_") // I assume it's not valid in filament
        .chars()
        .skip(1) // spade prefixes with a \
        .collect::<String>();

    let mut context = ComponentBuilderContext::default();
    let mut builder = FilamentComponentBuilder::new_in(ctx, comp_ctx, name);

    build_signature(&mut context, &mut builder, entity);
    extract_instances(&mut context, &mut builder, entity);
    construct_invocations(&mut context, &mut builder, entity);

    // hack
    let idx = builder.idx();
    ctx.entrypoint = Some(fil_ir::EntryPoint::new(idx));
}

pub fn build_fil_ctx(mir: &[Codegenable], lib: Vec<PathBuf>) -> fil_ir::Context {
    let mut prelude = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    prelude.push("resources/prelude.fil");
    let namespace = match fil::resolver::Resolver::new(lib, prelude).parse_namespace() {
        Ok(namespace) => namespace,
        Err(err) => panic!("invalid standard library: {:?}", err),
    };

    let mut ctx = fil_ir::transform(namespace).expect("invalid standard library");

    let mut comp_map = BiMap::new();
    let mut sig_map = fil_ir::DenseIndexInfo::default();
    for (idx, comp) in ctx.comps.iter() {
        if let Some(name) = comp.source_name().map(|id| id.to_string()) {
            println!("{}", name);
            comp_map.insert(name, idx);
        }
        sig_map.insert(idx, FilamentSignature::from(comp));
    }
    let comp_ctx = FilamentGlobalContext { comp_map, sig_map };

    for entity in mir {
        if entity.0.pipeline_latency.is_some() {
            build_fil_comp(&mut ctx, &comp_ctx, &entity.0);
        }
    }

    ctx
}

pub fn print_fil_ctx(ctx: &fil_ir::Context) -> io::Result<()> {
    for (idx, comp) in ctx.comps.iter().filter(|(_, comp)| !comp.is_ext()) {
        fil_ir::Printer::new(comp)
            .with_ctx(ctx)
            .comp(Some(idx), &mut io::stdout())?;
    }
    Ok(())
}

pub fn lower_fil_ctx(mut ctx: fil_ir::Context) -> Result<calyx_ir::Context, u64> {
    let opts = &fil::cmdline::Opts {
        input: PathBuf::from("<internal>"),
        dump_after: vec![],
        show_models: false,
        library: vec![],
        check: false,
        dump_interface: false,
        log_level: log::LevelFilter::Off,
        unsafe_skip_discharge: false,
        out_dir: None,
        bindings: None,
        backend: fil::cmdline::Backend::Calyx,
        no_counter_fsms: true,
        preserve_names: true,
        solver: fil::cmdline::Solver::CVC5,
        discharge_separate: false,
        solver_replay_file: None,
        solver_bv: None,
    };
    fil::ir_pass_pipeline2! { opts, ctx;
        fil_ip::BuildDomination,
        // fil_ip::TypeCheck,
        // fil_ip::IntervalCheck,
        // fil_ip::PhantomCheck,
        fil_ip::Assume
    }
    if !opts.unsafe_skip_discharge {
        fil::ir_pass_pipeline2! {opts, ctx; fil_ip::Discharge }
    }
    fil::ir_pass_pipeline2! { opts, ctx;
        fil_ip::BuildDomination
    };
    let mut gen_exec = None;
    ctx = fil_ip::Monomorphize::transform(&ctx, &mut gen_exec);
    fil::ir_pass_pipeline2! { opts, ctx;
        fil_ip::FSMAttributes,
        fil_ip::Simplify,
        fil_ip::AssignCheck,
        fil_ip::BundleElim,
        fil_ip::AssignCheck
    }

    let calyx = fil_ip::Compile::compile(ctx, opts.preserve_names);

    calyx_ir::Printer::write_context(&calyx, true, &mut std::io::stdout()).unwrap();

    Ok(calyx)
}
