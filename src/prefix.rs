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

        let p = Prefix::<Ipv4Addr>::from_str("1.2.3.4").unwrap();
        assert_eq!(p.address().octets(), [1, 2, 3, 4]);
        assert_eq!(p.to_string(), "1.2.3.4/32");

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

        match Prefix::<Ipv6Addr>::from_str("2001:1234::/130") {
            Ok(_) => assert!(false, "Should return error"),
            Err(err) => { }
        }
    }
}
