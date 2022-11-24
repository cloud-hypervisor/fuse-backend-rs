
#![allow(missing_docs)]

use std::collections::{HashMap, LinkedList};
use std::io::Result;
use std::sync::{Arc};
use std::io::{Error, ErrorKind};
use libc;

use self::super::layer::Layer;
use self::super::PLUGIN_PREFIX;
use self::super::direct::Direct;
use self::super::BoxedLayer;

pub type BoxedPlugin = Box<dyn Plugin + Send + Sync>;

/// ! plugin trait
pub trait Plugin {
	///! name
	fn name(&self) -> String;
	///! load data source
	fn load(&self, opaque: String, upper: bool) -> Result<LinkedList<Arc<BoxedLayer>>>;
	///! release plugin
	fn release(&self) -> Result<()>;
}

///! plugin manager
pub struct PluginManager {
	///! inner data
	pub plugins: HashMap<String, Arc<Box<dyn Plugin + Send + Sync>>>,
}

impl PluginManager {
	///! new
	pub fn new() -> Self {
		PluginManager {
			plugins: HashMap::new(),
		}
	}

	///! register a plugin
	pub fn register(&mut self, name: String, plugin: Arc<Box<dyn Plugin + Send + Sync>>) -> Result<()> {
		if self.plugins.get(name.as_str()).is_some() {
			return Err(Error::from_raw_os_error(libc::EEXIST));
		}
		self.plugins.insert(name, plugin);

		Ok(())
	}

	///! find a registerd plugin
	pub fn get_plugin(&self, name: String) -> Option<Arc<Box<dyn Plugin + Send + Sync>>> {
		if let Some(ref v) = self.plugins.get(name.as_str()) {
			Some(Arc::clone(v))
		} else {
			None
		}
	}
}

pub fn find_plugin(manager: &PluginManager, name: String) -> Option<Arc<Box<dyn Plugin + Send + Sync>>> {
	manager.get_plugin(name)
}

pub fn process_onelayer(manager: &PluginManager, opaque: String, upper: bool) -> Result<LinkedList<Arc<BoxedLayer>>> {
	if opaque.starts_with(PLUGIN_PREFIX) {
		// plugin
		let striped = opaque.strip_prefix(PLUGIN_PREFIX).unwrap();
		let ps: Vec<&str> = striped.splitn(2, "/").collect();
		if ps.len() != 2 {
			error!("invalid upperdir parameters!");
			return Err(Error::from(ErrorKind::InvalidData));
		}

		let plugin_name = ps[0];
		let plugin_params = ps[1];
		let plugin = match manager.get_plugin(plugin_name.into()) {
			Some(v) => v,
			None => {
				error!("unknown plugin");
				return Err(Error::from(ErrorKind::InvalidData));
			}
		};

		// load layers from plugin
		return plugin.load(plugin_params.into(), upper);

	} else {
		// directory
		return Direct::new(opaque, upper);
	}
}
