use std::fmt::{self, Debug, Formatter};

/// Helper for printing comma-separated items.
pub struct CommaSeparated<I: IntoIterator, F: Fn() -> I>(pub F) where I::Item: Debug;

impl<I: IntoIterator, F: Fn() -> I> Debug for CommaSeparated<I, F> where I::Item: Debug {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        let mut sep = "";
        for item in self.0() {
            f.write_str(sep)?;
            item.fmt(f)?;
            sep = ", ";
        }
        Ok(())
    }
}
