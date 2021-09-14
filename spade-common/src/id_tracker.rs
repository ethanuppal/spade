macro_rules! def_id_tracker {
    ($name:ident) => {
        pub struct $name {
            id: u64,
        }

        impl $name {
            pub fn new() -> Self {
                Self { id: 0 }
            }

            pub fn next(&mut self) -> u64 {
                let result = self.id;
                self.id += 1;
                result
            }

            /// Clone this ID tracker. After this is done, only one of the ID trackers may
            /// be used otherwise duplicate IDs will be generated. It is up to the caller of this
            /// method to make sure that no mutable references are handed out to one of the clonse
            pub fn make_clone(&self) -> Self {
                Self { id: self.id }
            }
        }
    };
}

def_id_tracker!(NameIdTracker);
def_id_tracker!(ExprIdTracker);
