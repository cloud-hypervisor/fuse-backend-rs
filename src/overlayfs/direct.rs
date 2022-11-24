use std::collections::LinkedList;
use std::sync::Arc;
use std::io::{Result, Error, ErrorKind};


use self::super::layer::Layer;

pub struct Direct {
}

impl Direct {
	pub fn new(path: String) -> Result<LinkedList<Arc<Box<dyn Layer>>>> {
		Err(Error::from(ErrorKind::Unsupported))
	}
}

impl Layer for Direct {
}
