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
///
fn take_while<'a, F, I>(condition: F) -> impl Fn(&'a [u8]) -> KResult<&'a str, &'a str>
where
    I: From<u8>,
    F: Fn(I) -> bool,
{
    move |source| {
        if let Some(index) = source.iter().position(|&e| condition(e.into())) {
            let input = std::str::from_utf8(&source[index + 1..]).expect("This should work bruh");
            let result =
                std::str::from_utf8(&source[index..index + 1]).expect("This should work bruh");
            Ok((input, result))
        } else {
            Err(ParserError::NoMatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_test() {
        let parse = tag("#");
        assert_eq!(parse(b"#123"), Ok(("123", "#")));
        assert_eq!(parse(b"max#balej"), Ok(("balej", "#")))
    }

    #[test]
    fn take_while_n_test() {
        let parse = take_while(is_digit);

        assert_eq!(parse(b"max123"), Ok(("23", "1")));
        assert_eq!(parse(b"12max"), Ok(("2max", "1")));
    }
    #[test]
    fn test_http_response_header() {
        let input = "HTTP/1.2 200 OK";

        let test: &[u8] = &[1, 2, 3, 4];
        let e = test[0];

        let (input, http) = tag("HTTP")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, slash) = tag("/")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, number1) =
            take_while(is_digit)(input.as_bytes()).expect("This should work, this is a bug");

        let (input, dot) = tag(".")(input.as_bytes()).expect("This should work, this is a bug");

        let (input, number2) =
            take_while(is_digit)(input.as_bytes()).expect("This should work, this is a bug");

        // let (input, slash) =
        //     take_while_n(1, is_digit)(input.as_bytes()).expect("This should work, this is a bug");

        assert_eq!(http, "HTTP");
        assert_eq!(slash, "/");
        assert_eq!(number1, "1");
        assert_eq!(dot, ".");
        assert_eq!(number2, "2");
    }
}
