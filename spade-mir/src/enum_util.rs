pub fn tag_size(variant_count: usize) -> usize {
    (variant_count as f32).log2().ceil() as usize
}
