//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//
// IP Prefix - abstract IPv? address and prefix length.
//

use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::str::FromStr;
use std::error::Error;
use std::fmt;
    
///
/// Trait to extend IpAddr.
///
pub trait AddressLen {
    /// Return address length in bits.
    fn address_len() -> u8;

    /// Construct address with all 0s.
    fn empty_new() -> Self;
}

impl AddressLen for Ipv4Addr {
    /// Return address length in bits.
    fn address_len() -> u8 {
        32
    }

    /// Construct address with all 0s.
    fn empty_new() -> Self {
        Ipv4Addr::new(0, 0, 0, 0)
    }
}

impl AddressLen for Ipv6Addr {
    /// Return address length in bits.
    fn address_len() -> u8 {
        128
    }

    /// Construct address with all 0s.
    fn empty_new() -> Self {
        Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0)
    }
}

///
/// Trait Prefixable.
///
pub trait Prefixable {
    /// Construct prefix from prefix.
    fn from_prefix(p: &Self) -> Self;

    /// Construct a prefix from common parts of two prefixes.
    fn from_common(prefix1: &Self, prefix2: &Self) -> Self;

    /// Return prefix length.
    fn len(&self) -> u8;

    /// Return 0 or 1 at certain position of bit in the prefix.
    fn bit_at(&self, index: u8) -> u8 {
        let offset = index / 8;
        let shift = 7 - (index % 8);
        let octets = self.octets();

        (octets[offset as usize] >> shift) & 0x1
    }

    /// Return reference of slice to address.
    fn octets(&self) -> &[u8];

    /// Return mutable reference of slice to address.
    fn octets_mut(&mut self) -> &mut [u8];

    /// Return true if given prefix is included in this prefix.
    fn contains(&self, prefix: &Self) -> bool {
        if self.len() > prefix.len() {
            return false
        }

        let np = self.octets();
        let pp = prefix.octets();

        let mut offset: u8 = self.len() / 8;
        let shift: u8 = self.len() % 8;

        if shift > 0 {
            if (MASKBITS[shift as usize] & (np[offset as usize] ^ pp[offset as usize])) > 0 {
                return false
            }
        }

        while offset > 0 {
            offset -= 1;
            if np[offset as usize] != pp[offset as usize] {
                return false
            }
        }

        return true
    }
}

///
/// Bitmask utilities.
///
const PLEN2MASK: [[u8; 4]; 32] = [
    [0x00, 0x00, 0x00, 0x00],
    [0x80, 0x00, 0x00, 0x00],
    [0xc0, 0x00, 0x00, 0x00],
    [0xe0, 0x00, 0x00, 0x00],
    [0xf0, 0x00, 0x00, 0x00],
    [0xf8, 0x00, 0x00, 0x00],
    [0xfc, 0x00, 0x00, 0x00],
    [0xfe, 0x00, 0x00, 0x00],

    [0xff, 0x00, 0x00, 0x00],
    [0xff, 0x80, 0x00, 0x00],
    [0xff, 0xc0, 0x00, 0x00],
    [0xff, 0xe0, 0x00, 0x00],
    [0xff, 0xf0, 0x00, 0x00],
    [0xff, 0xf8, 0x00, 0x00],
    [0xff, 0xfc, 0x00, 0x00],
    [0xff, 0xfe, 0x00, 0x00],

    [0xff, 0xff, 0x00, 0x00],
    [0xff, 0xff, 0x80, 0x00],
    [0xff, 0xff, 0xc0, 0x00],
    [0xff, 0xff, 0xe0, 0x00],
    [0xff, 0xff, 0xf0, 0x00],
    [0xff, 0xff, 0xf8, 0x00],
    [0xff, 0xff, 0xfc, 0x00],
    [0xff, 0xff, 0xfe, 0x00],

    [0xff, 0xff, 0xff, 0x00],
    [0xff, 0xff, 0xff, 0x80],
    [0xff, 0xff, 0xff, 0xc0],
    [0xff, 0xff, 0xff, 0xe0],
    [0xff, 0xff, 0xff, 0xf0],
    [0xff, 0xff, 0xff, 0xf8],
    [0xff, 0xff, 0xff, 0xfc],
    [0xff, 0xff, 0xff, 0xfe],
];

const PLEN2MASK6: [u16; 16] = [
    0x0000,
    0x8000,
    0xc000,
    0xe000,
    0xf000,
    0xf800,
    0xfc00,
    0xfe00,

    0xff00,
    0xff80,
    0xffc0,
    0xffe0,
    0xfff0,
    0xfff8,
    0xfffc,
    0xfffe,
];

const MASKBITS: [u8; 9] = [
    0x00, 0x80, 0xc0, 0xe0,
    0xf0, 0xf8, 0xfc, 0xfe, 0xff
];

/// Get 4 u8 values from slices and return u32 in network byte order.
fn slice_get_u32(s: &[u8], i: usize) -> u32 {
    ((s[i] as u32) << 24) | ((s[i + 1] as u32) << 16) | ((s[i + 2] as u32) << 8) | s[i + 3] as u32
}

/// Copy u32 value to slice.
fn slice_copy_u32(s: &mut [u8], v: u32, i: usize) {
    s[i + 0] = ((v >> 24) & 0xFF) as u8;
    s[i + 1] = ((v >> 16) & 0xFF) as u8;
    s[i + 2] = ((v >> 8) & 0xFF) as u8;
    s[i + 3] = (v & 0xFF) as u8;
}

///
/// IP Prefix.
///
#[derive(Debug, Clone, Copy)]
pub struct Prefix<T> {
    // IP Address.
    address: T,

    // Prefix Length.
    len: u8,
}

// 
impl<T: AddressLen + Clone> Prefixable for Prefix<T> {
    /// Duplicate prefix.
    fn from_prefix(p: &Self) -> Self {
        Self {
            address: p.address.clone(),
            len: p.len
        }
    }

    /// Construct a prefix from common parts of two prefixes, assuming p1 is shorter than p2.
    fn from_common(prefix1: &Self, prefix2: &Self) -> Self {
        let p1 = prefix1.octets();
        let p2 = prefix2.octets();
        let mut i = 0u8;
        let mut j = 0u8;
        let mut pcommon = Self { address: T::empty_new(), len: 0 };
        let px = pcommon.octets_mut();
        let bytes = T::address_len() / 8;

        while i < bytes {
            let l1: u32 = slice_get_u32(p1, i as usize);
            let l2: u32 = slice_get_u32(p2, i as usize);
            let cp: u32 = l1 ^ l2;
            if cp == 0 {
                slice_copy_u32(px, l1, i as usize);
            }
            else {
                j = cp.leading_zeros() as u8;
                let (mask, _) = match j {
                    0 => (0, false),
                    _ => 0xFFFFFFFFu32.overflowing_shl((32 - j) as u32),
                };
                let v = l1 & (mask as u32);

                slice_copy_u32(px, v, i as usize);
                break;
            }

            i += 4;
        }

        pcommon.len = if prefix2.len() > i * 8 + j {
            i * 8 + j
        } else {
            prefix2.len()
        };

        pcommon
    }

    /// Return prefix length.
    fn len(&self) -> u8 {
        self.len
    }

    /// Return reference of slice to address.
    fn octets(&self) -> &[u8] {
        let p = (&self.address as *const T) as *const u8;
        unsafe {
            std::slice::from_raw_parts(p, std::mem::size_of::<T>())
        }
    }

    /// Return mutable reference of slice to address.
    fn octets_mut(&mut self) -> &mut [u8] {
        let p = (&mut self.address as *mut T) as *mut u8;
        unsafe {
            std::slice::from_raw_parts_mut(p, std::mem::size_of::<T>())
        }
    }
}

///
/// Abstract IPv4 and IPv6 both.
///
impl<T: AddressLen + FromStr> Prefix<T> {
    /// Construct prefix from string slice.
    pub fn from_str(s: &str) -> Result<Prefix<T>, PrefixParseError> {
        let (pos, prefix_len) = match s.find('/') {
            // Address with prefix length.
            Some(pos) => {
                match s[pos + 1..].parse::<u8>() {
                    Ok(prefix_len) if prefix_len <= T::address_len() => (pos, prefix_len),
                    _ => return Err(PrefixParseError(())),
                }
            },
            // Consider host address.
            None => (s.len(), T::address_len()),
        };
                    
        let address_str = &s[..pos];
        match T::from_str(address_str) {
            Ok(address) =>
                Ok(Prefix::<T> {
                    address: address,
                    len: prefix_len,
                }),
            Err(_) => Err(PrefixParseError(())),
        }
    }

    /// Return address part of prefix.
    pub fn address(&self) -> &T {
        &self.address
    }
}

/// Impl IPv4 Prefix.
impl Prefix<Ipv4Addr> {
    /// Apply network mask to address part.
    pub fn apply_mask(&mut self) {
        if self.len < Ipv4Addr::address_len() {
            let octets = self.address().octets();
            let mask = &PLEN2MASK[self.len as usize];
            self.address = Ipv4Addr::new(octets[0] & mask[0],
                                         octets[1] & mask[1],
                                         octets[2] & mask[2],
                                         octets[3] & mask[3]);
        }
    }
}

/// Impl IPv6 Prefix.
impl Prefix<Ipv6Addr> {
    /// Apply network mask to address part.
    pub fn apply_mask(&mut self) {
        fn mask4segment(s: u8, len: u8) -> u16 {
            if len >= s * 16 {
                let offset = len - s * 16;
                if offset >= 16 {
                    0xffff
                }
                else {
                    PLEN2MASK6[offset as usize]
                }
            }
            else {
                0
            }
        }

        if self.len < Ipv6Addr::address_len() {
            let segments = self.address().segments();
            self.address = Ipv6Addr::new(segments[0] & mask4segment(0, self.len),
                                         segments[1] & mask4segment(1, self.len),
                                         segments[2] & mask4segment(2, self.len),
                                         segments[3] & mask4segment(3, self.len),
                                         segments[4] & mask4segment(4, self.len),
                                         segments[5] & mask4segment(5, self.len),
                                         segments[6] & mask4segment(6, self.len),
                                         segments[7] & mask4segment(7, self.len));
        }
    }
}

impl<T: AddressLen + ToString> fmt::Display for Prefix<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}/{}", self.address.to_string(), self.len)
    }
}

///
/// Prefix Parse Error.
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrefixParseError(());

impl fmt::Display for PrefixParseError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_str(self.description())
    }
}

impl Error for PrefixParseError {
    fn description(&self) -> &str {
        "invalid IP prefix syntax"
    }
}

///
/// Unit tests for Prefix.
///
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_octets() {
        let p = Prefix::<Ipv4Addr>::from_str("1.2.3.4/24").unwrap();
        let o = p.octets();
        assert_eq!(o, &[1, 2, 3, 4]);

        let p = Prefix::<Ipv6Addr>::from_str("2001:1:2::7:8/48").unwrap();
        let o = p.octets();
        assert_eq!(o, &[0x20, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 7, 0, 8]);
    }

    #[test]
    pub fn test_prefix_ipv4() {
        let p = Prefix::<Ipv4Addr>::from_str("10.10.10.0/24").unwrap();
        assert_eq!(p.address().octets(), [10, 10, 10, 0]);
        assert_eq!(p.to_string(), "10.10.10.0/24");

        let p = Prefix::<Ipv4Addr>::from_str("1.2.3.4").unwrap();
        assert_eq!(p.address().octets(), [1, 2, 3, 4]);
        assert_eq!(p.to_string(), "1.2.3.4/32");

        let mut p = Prefix::<Ipv4Addr>::from_str("1.2.3.4/24").unwrap();
        assert_eq!(p.address().octets(), [1, 2, 3, 4]);
        assert_eq!(p.to_string(), "1.2.3.4/24");
        p.apply_mask();
        assert_eq!(p.address().octets(), [1, 2, 3, 0]);
        assert_eq!(p.to_string(), "1.2.3.0/24");

        let mut p = Prefix::<Ipv4Addr>::from_str("172.16.0.1/16").unwrap();
        assert_eq!(p.address().octets(), [172, 16, 0, 1]);
        assert_eq!(p.to_string(), "172.16.0.1/16");
        p.apply_mask();
        assert_eq!(p.address().octets(), [172, 16, 0, 0]);
        assert_eq!(p.to_string(), "172.16.0.0/16");

        match Prefix::<Ipv4Addr>::from_str("10.10.10.10/33") {
            Ok(_) => assert!(false, "Should return error"),
            Err(_err) => { }
        }
    }

    #[test]
    pub fn test_prefix_ipv4_common() {
        let p1 = Prefix::<Ipv4Addr>::from_str("10.10.10.0/24").unwrap();
        let p2 = Prefix::<Ipv4Addr>::from_str("10.10.11.0/24").unwrap();
        let pc = Prefix::<Ipv4Addr>::from_common(&p1, &p2);
        assert_eq!(pc.to_string(), "10.10.10.0/23");

        let p1 = Prefix::<Ipv4Addr>::from_str("10.10.10.0/24").unwrap();
        let p2 = Prefix::<Ipv4Addr>::from_str("10.10.0.0/16").unwrap();
        let pc = Prefix::<Ipv4Addr>::from_common(&p1, &p2);
        assert_eq!(pc.to_string(), "10.10.0.0/16");

        let p1 = Prefix::<Ipv4Addr>::from_str("192.168.0.0/24").unwrap();
        let p2 = Prefix::<Ipv4Addr>::from_str("10.10.10.0/24").unwrap();
        let pc = Prefix::<Ipv4Addr>::from_common(&p1, &p2);
        assert_eq!(pc.to_string(), "0.0.0.0/0");

        let p1 = Prefix::<Ipv4Addr>::from_str("192.168.0.0/24").unwrap();
        let p2 = Prefix::<Ipv4Addr>::from_str("128.10.10.0/24").unwrap();
        let pc = Prefix::<Ipv4Addr>::from_common(&p1, &p2);
        assert_eq!(pc.to_string(), "128.0.0.0/1");
    }

    #[test]
    pub fn test_prefix_ipv6() {
        let p = Prefix::<Ipv6Addr>::from_str("::/0").unwrap();
        assert_eq!(p.address().segments(), [0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(p.to_string(), "::/0");

        let p = Prefix::<Ipv6Addr>::from_str("2001:1234::/48").unwrap();
        assert_eq!(p.address().segments(), [0x2001, 0x1234, 0, 0, 0, 0, 0, 0]);
        assert_eq!(p.to_string(), "2001:1234::/48");

        let mut p = Prefix::<Ipv6Addr>::from_str("2001:1234::567/48").unwrap();
        assert_eq!(p.address().segments(), [0x2001, 0x1234, 0, 0, 0, 0, 0, 0x567]);
        assert_eq!(p.to_string(), "2001:1234::567/48");
        p.apply_mask();
        assert_eq!(p.address().segments(), [0x2001, 0x1234, 0, 0, 0, 0, 0, 0]);
        assert_eq!(p.to_string(), "2001:1234::/48");

        let mut p = Prefix::<Ipv6Addr>::from_str("2001:1234::ffff/124").unwrap();
        p.apply_mask();
        assert_eq!(p.address().segments(), [0x2001, 0x1234, 0, 0, 0, 0, 0, 0xfff0]);
        assert_eq!(p.to_string(), "2001:1234::fff0/124");

        let mut p = Prefix::<Ipv6Addr>::from_str("2001:1234::ffff/120").unwrap();
        p.apply_mask();
        assert_eq!(p.address().segments(), [0x2001, 0x1234, 0, 0, 0, 0, 0, 0xff00]);
        assert_eq!(p.to_string(), "2001:1234::ff00/120");

        match Prefix::<Ipv6Addr>::from_str("2001:1234::/130") {
            Ok(_) => assert!(false, "Should return error"),
            Err(_err) => { }
        }
    }
}
