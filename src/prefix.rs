//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

//use std::error::Error;
//use std::net::IpAddr;
use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::net::AddrParseError;
use std::str::FromStr;
use std::error::Error;
use std::fmt;
    
type V4 = Ipv4Addr;
type V6 = Ipv6Addr;

// IP Prefix.
#[derive(Debug)]
struct Prefix<A> {
    // IP Address.
    address: A,

    // Prefix Length.
    len: u8,
}

// IPv4 Prefix specialization.
impl Prefix<V4> {
    pub fn from_str(s: &str) -> Result<Prefix<V4>, PrefixParseError> {
        match s.find('/') {
            // Address with prefix length.
            Some(pos) => {
                match s[pos + 1..].parse::<u8>() {
                    Ok(prefix_len) if prefix_len <= 32 => {
                        let address_str = &s[..pos];
                        match Ipv4Addr::from_str(address_str) {
                            Ok(address) =>
                                Ok(Prefix {
                                    address: address,
                                    len: prefix_len,
                                }),
                            Err(_) => Err(PrefixParseError(())),
                        }
                    },
                    _ => Err(PrefixParseError(())),
                }
            },
            // Consider host address.
            None => {
                match Ipv4Addr::from_str(s) {
                    Ok(address) =>
                        Ok(Prefix {
                            address: address,
                            len: 32,
                        }),
                    Err(_) => Err(PrefixParseError(())),
                }
            }
        }
    }
}

impl fmt::Display for Prefix<V4> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}/{}", self.address.to_string(), self.len)
    }
}

// IPv6 Prefix specialization.
impl Prefix<V6> {
    pub fn from_str(s: &str) -> Result<Prefix<V6>, PrefixParseError> {
        match s.find('/') {
            // Address with prefix length.
            Some(pos) => {
                match s[pos + 1..].parse::<u8>() {
                    Ok(prefix_len) if prefix_len <= 128 => {
                        let address_str = &s[..pos];
                        match Ipv6Addr::from_str(address_str) {
                            Ok(address) =>
                                Ok(Prefix {
                                    address: address,
                                    len: prefix_len,
                                }),
                            Err(_) => Err(PrefixParseError(())),
                        }
                    },
                    _ => Err(PrefixParseError(())),
                }
            },
            // Consider host address.
            None => {
                match Ipv6Addr::from_str(s) {
                    Ok(address) =>
                        Ok(Prefix {
                            address: address,
                            len: 128,
                        }),
                    Err(_) => Err(PrefixParseError(())),
                }
            }
        }
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
        let p = Prefix::<V4>::from_str("10.10.10.0/24").unwrap();
        assert_eq!(p.to_string(), "10.10.10.0/24");

        let p = Prefix::<V4>::from_str("10.10.10.10").unwrap();
        assert_eq!(p.to_string(), "10.10.10.10/32");

        match Prefix::<V4>::from_str("10.10.10.10/33") {
            Ok(_) => assert!(false, "Should return error"),
            Err(err) => { }
        }
    }
}
