#![allow(dead_code, unused_variables)]
//! # Parser Kombinator
//!
//! Kombinator is a simple parser combinator that I made
//! to parse http request/response headers

/// Generic parser errors
#[derive(Debug, PartialEq)]
pub enum ParserError {
    NoMatch,
}
/// Parsing Result type
pub type KResult<I, O, E = ParserError> = Result<(I, O), E>;

/// Find the pattern from source and slice
/// the input from the index
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // Define the pattern
/// let parse = tag("#");
///
/// assert_eq!(parse(b"#123"), Ok(("123", "#")));
/// assert_eq!(parse(b"hello#world"), Ok(("world", "#")))
/// ```
pub fn tag(pattern: &str) -> impl Fn(&[u8]) -> KResult<&str, &str> + '_ {
    move |source| {
        let source_to_utf8 = std::str::from_utf8(source).expect("Coulnd't transform to utf8");

        if let Some(index) = source_to_utf8.find(pattern) {
            Ok((
                &source_to_utf8[index + 1..],
                &source_to_utf8[index..index + pattern.len()],
            ))
        } else {
            Err(ParserError::NoMatch)
        }
    }
}

/// Checks if char is an ascii digit
pub fn is_digit(char: char) -> bool {
    char.is_ascii_digit()
}
/// Iterates over the input and slice the source
/// if it respect the condition
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // Define the parser
/// let parse = take_while(is_digit);
///
/// assert_eq!(parse(b"max123"), Ok(("23", "1")));
/// assert_eq!(parse(b"12max"), Ok(("2max", "1")));
/// ```
// fn take_while<I: IntoIterator, F: Fn(I) -> bool>(
//     condition: F,
// ) -> impl Fn(I) -> PResult<&str, &str> {
//     move |source| {
//         // let source_to_utf8 = std::str::from_utf8(source).expect("Coulnd't transform to utf8");
//         for (idx, byte) in source.into_iter().enumerate() {
//             if condition(byte) {
//                 return Ok((&source_to_utf8[idx + 1..], &source_to_utf8[idx..idx + 1]));
//             }
//         }
//
//         Err(ParserError::NoMatch)
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_test() {
        let parse = tag("#");
        assert_eq!(parse(b"#123"), Ok(("123", "#")));
        assert_eq!(parse(b"max#balej"), Ok(("balej", "#")))
    }

    // #[test]
    // fn take_while_n_test() {
    //     let parse = take_while(is_digit);
    //
    //     assert_eq!(parse(b"max123"), Ok(("23", "1")));
    //     assert_eq!(parse(b"12max"), Ok(("2max", "1")));
    // }
    #[test]
    fn test_http_response_header() {
        let input = "HTTP/1.x 200 OK";
        let (input, http) = tag("HTTP")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, slash) = tag("/")(input.as_bytes()).expect("This should work, this is a bug");
        // let (input, slash) =
        //     take_while_n(1, is_digit)(input.as_bytes()).expect("This should work, this is a bug");

        assert_eq!(http, "HTTP");
        assert_eq!(slash, "/");
    }
}
