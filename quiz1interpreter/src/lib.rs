use patronus;

/// Loads a BTOR2 file and returns the context and transition system
/// 
/// # Arguments
/// * `path` - Path to the BTOR2 file
/// 
/// # Returns
/// * `Result<(Context, TransitionSystem), Box<dyn std::error::Error>>` - The parsed context and transition system, or an error
pub fn load_btor2_file(path: &str) -> Result<(patronus::expr::Context, patronus::system::TransitionSystem), Box<dyn std::error::Error>> {
    let (ctx, ts) = patronus::btor2::parse_file(path).ok_or("Failed to parse BTOR2 file")?;
    Ok((ctx, ts))
}

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
