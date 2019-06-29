//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//
// IP Prefix - abstract IPv? address and prefix length.
//

use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::net::AddrParseError;
use std::str::FromStr;
use std::error::Error;
use std::fmt;
    
// Trait to enhance IpAddr::*.
pub trait AddressLen {
    fn address_len() -> u8;
}

impl AddressLen for Ipv4Addr {
    fn address_len() -> u8 {
        32
    }
}

impl AddressLen for Ipv6Addr {
    fn address_len() -> u8 {
        128
    }
}

// Utilities.
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

// IP Prefix.
#[derive(Debug)]
struct Prefix<T> {
    // IP Address.
    address: T,

    // Prefix Length.
    len: u8,
}

// Abstract IPv4 and IPv6 both.
impl<T: AddressLen + FromStr> Prefix<T> {
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

    pub fn address(&self) -> &T {
        &self.address
    }
}

impl Prefix<Ipv4Addr> {
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

impl Prefix<Ipv6Addr> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_prefix_ipv4() {
        let p = Prefix::<Ipv4Addr>::from_str("10.10.10.0/24").unwrap();
        assert_eq!(p.address().octets(), [10, 10, 10, 0]);
        assert_eq!(p.to_string(), "10.10.10.0/24");

        let mut p = Prefix::<Ipv4Addr>::from_str("1.2.3.4").unwrap();
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
            Err(err) => { }
        }
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
            Err(err) => { }
        }
    }
}
