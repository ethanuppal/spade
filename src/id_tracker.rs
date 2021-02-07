pub struct IdTracker {
    id: u64,
}
impl IdTracker {
    pub fn new() -> Self {
        Self { id: 0 }
    }

    pub fn next(&mut self) -> u64 {
        let result = self.id;
        self.id += 1;
        result
    }
}
