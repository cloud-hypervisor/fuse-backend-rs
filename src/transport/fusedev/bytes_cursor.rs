use crate::transport::Error;
use std::{io, mem};

#[derive(Debug, Default)]
pub(crate) struct BytesCursor<'a> {
    slice: &'a mut [u8],
    /// position <= slice.len()
    position: usize,
}

impl<'a> BytesCursor<'a> {
    pub(crate) fn new(slice: &'a mut [u8], position: usize) -> Self {
        assert!(position <= slice.len());
        BytesCursor { slice, position }
    }

    pub(crate) fn slice_mut(&mut self) -> &mut [u8] {
        self.slice
    }

    pub(crate) fn position(&self) -> usize {
        self.position
    }

    pub(crate) fn available_bytes(&self) -> usize {
        self.slice.len() - self.position
    }

    pub(crate) fn check_available_space(&self, sz: usize) -> io::Result<()> {
        if sz > self.available_bytes() {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    self.available_bytes(),
                    sz
                ),
            ))
        } else {
            Ok(())
        }
    }

    pub(crate) fn available_slice(&mut self) -> &mut [u8] {
        &mut self.slice[self.position..]
    }

    pub(crate) fn account_written(&mut self, count: usize) {
        assert!(self.available_bytes() >= count);
        self.position += count;
    }

    pub(crate) fn written(&self) -> &[u8] {
        &self.slice[..self.position]
    }

    pub(crate) fn split_at(&mut self, offset: usize) -> Result<BytesCursor<'a>, Error> {
        if self.slice.len() < offset {
            return Err(Error::SplitOutOfBounds(offset));
        }

        let (len1, len2) = if self.position > offset {
            (offset, self.position - offset)
        } else {
            (self.position, 0)
        };
        let (slice1, slice2) = mem::take(&mut self.slice).split_at_mut(offset);
        *self = BytesCursor::new(slice1, len1);
        Ok(BytesCursor::new(slice2, len2))
    }

    pub(crate) fn extend_from_slice(&mut self, slice: &[u8]) {
        self.slice[self.position..][..slice.len()].copy_from_slice(slice);
        self.position += slice.len();
    }
}

#[cfg(test)]
mod tests {
    use crate::transport::fusedev::bytes_cursor::BytesCursor;

    #[test]
    fn test_split_at() {
        let mut array = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

        let mut b = BytesCursor::new(&mut array, 0);
        let mut b1 = b.split_at(4).unwrap();

        assert_eq!(&[0, 1, 2, 3], b.slice_mut());
        assert_eq!(0, b.position());
        assert_eq!(&[4, 5, 6, 7, 8, 9], b1.slice_mut());
        assert_eq!(0, b1.position());

        let mut b = BytesCursor::new(&mut array, 6);
        let mut b1 = b.split_at(4).unwrap();
        assert_eq!(&[0, 1, 2, 3], b.slice_mut());
        assert_eq!(4, b.position());
        assert_eq!(&[4, 5, 6, 7, 8, 9], b1.slice_mut());
        assert_eq!(2, b1.position());
    }

    #[test]
    fn test_extend_from_slice() {
        let mut array = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut b = BytesCursor::new(&mut array, 3);
        b.extend_from_slice(&[b'a', b'b']);
        assert_eq!(&[0, 1, 2, b'a', b'b', 5, 6, 7, 8, 9], b.slice);
        assert_eq!(5, b.position());
    }
}
