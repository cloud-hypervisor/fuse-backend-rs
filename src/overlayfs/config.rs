
use std::time::Duration;
use self::super::CachePolicy;
use std::fmt;

#[derive(Default, Clone, Debug)]
pub struct Config {
	pub upper: String,
	pub lower: Vec<String>,
	pub work: String,
	pub mountpoint: String,
	pub do_import: bool,
	pub writeback: bool,
	pub no_open: bool,
	pub no_opendir: bool,
	pub killpriv_v2: bool,
	pub no_readdir: bool,
	pub xattr: bool,
	pub xattr_permissions: bool,
	pub perfile_dax: bool,
	pub cache_policy: CachePolicy,
	pub attr_timeout: Duration,
	pub entry_timeout: Duration,
}

impl Default for CachePolicy {
	fn default() -> Self {
		CachePolicy::Auto
	}
}

impl Clone for CachePolicy {
	fn clone(&self) -> Self {
		match *self {
			CachePolicy::Never => CachePolicy::Never,
			CachePolicy::Always => CachePolicy::Always,
			CachePolicy::Auto => CachePolicy::Auto,
		}
	}
}

impl fmt::Debug for CachePolicy {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let policy = 
		match *self {
			CachePolicy::Never => "Never",
			CachePolicy::Always => "Always",
			CachePolicy::Auto => "Auto",
		};

		write!(f, "CachePolicy: {}", policy)
	}
}
