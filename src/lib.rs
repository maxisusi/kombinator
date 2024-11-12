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


enum CompareResult {
    Ok,
    Error
}

trait Compare<T> {
    fn compare(&self, comp: T) -> CompareResult;
}

impl<'a, 'b> Compare<&'b [u8]> for &'a [u8] {
    fn compare(&self, comp: &'b [u8]) -> CompareResult {
        let res = self.iter().zip(comp.iter()).position(|(a, b)| a != b);

        match res {
            Some(_) => CompareResult::Error,
            None => {
                if self.len() >= comp.len() {
                    CompareResult::Ok
                } else {
                    CompareResult::Error
                }
            }
        }

    }
}

impl <'a, 'b> Compare<&'b str>  for &'a[u8] {
    fn compare(&self, comp: &'b str) -> CompareResult {
        self.compare(comp.as_bytes())
    }
}

impl <'a, 'b> Compare<&'b str>  for &'a str {
    fn compare(&self, comp: &'b str) -> CompareResult {
        self.as_bytes().compare(comp.as_bytes())
    }
}

macro_rules! compare_impl {
    ($($N:expr)+) => {
        $(
        
            impl <'a> Compare<[u8; $N]>  for &'a[u8] {
                fn compare(&self, comp: [u8;$N]) -> CompareResult {
                    let res = self.iter().zip(comp.iter()).position(|(a, b)| a != b);

                    match res {
                        Some(_) => CompareResult::Error,
                        None => {
                            if self.len() >= comp.len() {
                                CompareResult::Ok
                            } else {
                                CompareResult::Error
                            }
                        }
                    }
                }
            }
            impl <'a, 'b> Compare<&[u8; $N]>  for &'a[u8; $N] {
                fn compare(&self, comp: &[u8;$N]) -> CompareResult {
                    let res = self.iter().zip(comp.iter()).position(|(a, b)| a != b);

                    match res {
                        Some(_) => CompareResult::Error,
                        None => {
                            if self.len() >= comp.len() {
                                CompareResult::Ok
                            } else {
                                CompareResult::Error
                            }
                        }
                    }
                }
            }
        )+
        
    };
}

compare_impl!(0 1 2 3 4 5 6 7 8 9 10);

trait InputLength {
    fn input_length(&self) -> usize;
}

impl<'a> InputLength for &'a str {
    fn input_length(&self) -> usize {
        self.len()
    }
}

// Imput length
impl<'a> InputLength for &'a [u8] {
    fn input_length(&self) -> usize {
        self.len()
    }
}


macro_rules! input_len_impl {
    ($($N:expr)+) => {
        $(
            impl<'a> InputLength for &'a [u8; $N] {
                fn input_length(&self) -> usize {
                    self.len()
                }
            }
        )+
    }
}

input_len_impl!(1 2 3 4 5 6 7 8 9 10);

trait InputTake: Sized {
    fn take(&self) -> Self;
    fn take_split(&self, count: usize) -> (Self,Self);
}

impl <'a> InputTake for &'a str {
    fn take_split(&self, count: usize) -> (Self,Self) {
        (&self[..count], &self[count..])
    }
    fn take(&self) -> Self {
        todo!()
    }
}



impl <'a> InputTake for &'a [u8] {
    fn take_split(&self, count: usize) -> (Self,Self) {
        let (prefix, sufix) = self.split_at(count);
        (prefix, sufix)
    }
    fn take(&self) -> Self {
        self
    }
}

// macro_rules! input_take_impl {
//     ($($N:expr)+) => {
//         $(
//             impl <'a> InputTake for &'a [u8;$N] {
//                 fn take_split(&self, count: usize) -> (Self,Self) {
//                     (&self[0..count], &self[count..])
//                 }
//                 fn take(&self) -> Self {
//                     self
//                 }
//             }
//         )+ 
//     };
// }
//
// input_take_impl!(1 2 3 4 5 6 7 8 9 10);




/// Match the the pattern
/// from the start of the source until
/// pattern lenght
///
/// TODO: define errors
/// # Examples
///
/// Basic usage:
/// ```rust
/// use kombinator::match;
///
/// // Define the parser
///
/// let parse = matching("http");
/// assert_eq!(parse(b"http 1"), Ok((" 1", "http")));
/// ```
#[deprecated(note = "please use `tag` instead")]
pub fn matching<'a>(pattern: &'a str) -> impl Fn(&'a [u8]) -> KResult<&'a str, &'a str> {
    move |source| {
        for (idx, ch) in pattern.chars().enumerate() {
            if source[idx] != ch as u8 {
                return Err(ParserError::NoMatch);
            }
        }

        let input =
            std::str::from_utf8(&source[pattern.len()..]).expect("Coulnd't convert value to utf8");
        let res =
            std::str::from_utf8(&source[..pattern.len()]).expect("Couldn't convert value to utf8");

        Ok((input, res))
    }
}
/// Find the pattern from source and slice
/// the input from the index
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use kombinator::tag;
///
/// // Define the pattern
/// let parse = tag("#");
///
/// assert_eq!(parse(b"#123"), Ok(("123", "#")));
/// assert_eq!(parse(b"hello#world"), Ok(("world", "#")))
/// ```
pub fn tag<I, E>(pattern: E) -> impl Fn(I) -> KResult<I, I>
where
    E: Clone + InputLength,
    I: Compare<E> + InputTake
{
    move |source| {
        let compare_result = source.compare(pattern.clone());
        let pattern_len = pattern.input_length();
        return match compare_result {
            CompareResult::Ok => { Ok(source.take_split(pattern_len)) },
            CompareResult::Error => Err(ParserError::NoMatch)
        }
    }
}

/// Checks if char is an ascii digit
pub fn is_digit(char: char) -> bool {
    char.is_ascii_digit()
}
/// Consume the input and slice
/// if it matches the predicate
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use kombinator::{take_while, is_digit};
///
/// // Define the parser
/// let parse = take_while(is_digit);
///
/// assert_eq!(parse(b"max123"), Ok(("", "123")));
/// assert_eq!(parse(b"12max"), Ok(("max", "12")));
/// ```
///
pub fn take_while<'a, F, I>(condition: F) -> impl Fn(&'a [u8]) -> KResult<&'a str, &'a str>
where
    I: From<u8>,
    F: Fn(I) -> bool,
{
    move |source| {
        if let Some(start_index) = source.iter().position(|&e| condition(e.into())) {
            let end_index = source[start_index..]
                .iter()
                .position(|ch| !condition(Into::into(*ch)))
                .unwrap_or(source.len());

            let input = std::str::from_utf8(&source[end_index..]).expect("This should work bruh");
            let result = std::str::from_utf8(&source[start_index..end_index])
                .expect("This should work bruh");
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
    // fn matching_test() {
    //     let parse = matching("http");
    //     assert_eq!(parse(b"http 1"), Ok((" 1", "http")));
    // }

    #[test]
    fn tag_test() {
        let parse = tag("#");
        let parsed = parse("#123");
        // assert_eq!(parse(b"#123"), Ok((b"123", b"#")));
        // assert_eq!(parse(b"max#balej"), Ok(("balej", "#")));

        let parse = tag("http")("hello");

        // assert_eq!(parse(b"httvp"), Err(ParserError::NoMatch));
        // assert_eq!(parse(b"http"), Ok(("", "http")));
    }

    #[test]
    fn take_while_test() {
        let parse = take_while(is_digit);

        assert_eq!(parse(b"max123"), Ok(("", "123")));
        assert_eq!(parse(b"12max"), Ok(("max", "12")));
    }

    #[test]
    fn test_http_response_header() {
        let input = "HTTP/1.2 200 OK";

        input.as_bytes()

        let (input, http) =
            matching("HTTP")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, slash) =
            matching("/")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, number1) =
            take_while(is_digit)(input.as_bytes()).expect("This should work, this is a bug");
        let (input, dot) =
            matching(".")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, number2) =
            take_while(is_digit)(input.as_bytes()).expect("This should work, this is a bug");
        let (input, space) =
            matching(" ")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, two_hundred) =
            take_while(is_digit)(input.as_bytes()).expect("This should work, this is a bug");
        let (input, space) =
            matching(" ")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, ok) =
            matching("OK")(input.as_bytes()).expect("This should work, this is a bug");

        assert_eq!(http, "HTTP");
        assert_eq!(slash, "/");
        assert_eq!(number1, "1");
        assert_eq!(dot, ".");
        assert_eq!(number2, "2");
        assert_eq!(space, " ");
        assert_eq!(two_hundred, "200");
        assert_eq!(space, " ");
        assert_eq!(ok, "OK");
    }
}
