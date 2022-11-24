
use std::time::Duration;

pub struct Config {
	pub upper: String,
	pub lower: Vec<String>,
	pub work: String,
	pub do_import: bool,
	pub writeback: bool,
	pub no_open: bool,
	pub no_opendir: bool,
	pub killpriv_v2: bool,
	pub no_readdir: bool,
	pub xattr: bool,
	pub perfile_dax: bool,
	pub attr_timeout: Duration,
	pub entry_timeout: Duration,
}
