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

/// Comparison Result
pub enum CompareResult {
    Ok,
    Error,
}

/// Operations to compare asbtract element together
pub trait Compare<T> {
    /// Compares itslef to another one and returns a [`CompareResult`]
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

impl<'a, 'b> Compare<&'b str> for &'a [u8] {
    fn compare(&self, comp: &'b str) -> CompareResult {
        self.compare(comp.as_bytes())
    }
}

impl<'a, 'b> Compare<&'b str> for &'a str {
    fn compare(&self, comp: &'b str) -> CompareResult {
        self.as_bytes().compare(comp.as_bytes())
    }
}

/// Operations to get the input length of abstract types
pub trait InputLength {
    /// Returns the length of the input as a `usize`
    fn input_length(&self) -> usize;
}

impl<'a> InputLength for &'a str {
    fn input_length(&self) -> usize {
        self.len()
    }
}

impl<'a> InputLength for &'a [u8] {
    fn input_length(&self) -> usize {
        self.len()
    }
}

impl InputLength for char {
    fn input_length(&self) -> usize {
        self.len_utf8()
    }
}

/// Operations to take input from abstract types
pub trait InputTake: Sized {
    /// Takes the ownership of the input
    fn take(&self) -> Self;
    /// Splits the input into two parts and takes the ownsership
    /// First self represents the suffix and the second self represents the prefix
    fn take_split(&self, count: usize) -> (Self, Self);
}

impl<'a> InputTake for &'a str {
    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.split_at(count);
        (suffix, prefix)
    }
    fn take(&self) -> Self {
        self
    }
}

impl<'a> InputTake for &'a [u8] {
    fn take_split(&self, count: usize) -> (Self, Self) {
        let (prefix, suffix) = self.split_at(count);
        (suffix, prefix)
    }
    fn take(&self) -> Self {
        self
    }
}

/// Operations to take as much input as possible
/// from the input until the predicate is false
pub trait InputTakeAtPosition: Sized {
    type Item;

    /// Split at position where the predicate doesn't match
    /// the input
    fn split_at_position<P>(&self, predicate: P) -> KResult<Self, Self>
    where
        P: Fn(Self::Item) -> bool;

    /// Split at position where the predicate doesn't match
    /// the input but stop iterating at the specifie boundary
    fn split_at_bounded_position<P>(&self, boundary: usize, predicate: P) -> KResult<Self, Self>
    where
        P: Fn(Self::Item) -> bool;
}

impl<'a> InputTakeAtPosition for &'a str {
    type Item = u8;
    fn split_at_position<P>(&self, predicate: P) -> KResult<Self, Self>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.as_bytes().iter().position(|e| predicate(*e)) {
            Some(e) => Ok(self.take_split(e)),
            None => Err(ParserError::NoMatch),
        }
    }
    fn split_at_bounded_position<P>(&self, boundary: usize, predicate: P) -> KResult<Self, Self>
    where
        P: Fn(Self::Item) -> bool,
    {
        match self.as_bytes()[..boundary]
            .iter()
            .position(|e| predicate(*e))
        {
            Some(e) => Ok(self.take_split(e)),
            None => Ok(self.take_split(boundary)),
        }
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
/// use kombinator::{tag, ParserError};
///
/// // Define the pattern
/// let parse = tag("#");
///
/// assert_eq!(parse("#123"), Ok(("123", "#")));
/// assert_eq!(parse("hello#world"), Err(ParserError::NoMatch))
/// ```
pub fn tag<I, E>(pattern: E) -> impl Fn(I) -> KResult<I, I>
where
    E: Clone + InputLength,
    I: Compare<E> + InputTake,
{
    move |source| {
        let compare_result = source.compare(pattern.clone());
        let pattern_len = pattern.input_length();
        match compare_result {
            CompareResult::Ok => Ok(source.take_split(pattern_len)),
            CompareResult::Error => Err(ParserError::NoMatch),
        }
    }
}

/// Operations that represents a parser
pub trait Parser<I> {
    fn parse(&self, source: I) -> KResult<I, I>;
}

impl<I, F> Parser<I> for F
where
    F: Fn(I) -> KResult<I, I>,
{
    fn parse(&self, source: I) -> KResult<I, I> {
        self(source)
    }
}

/// Transform the result of a Parsing
/// function to another type
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use kombinator::{map_res, tag};
///
/// // Define the parsers
/// let parse_one = tag("1");
///
/// let to_string = map_res(&parse_one, |suffix: &str| suffix.to_string());
/// let to_digit = map_res(&parse_one, |suffix: &str| suffix.parse::<usize>().unwrap());
///
/// assert_eq!(to_string("123"), Ok(("23", "1".to_string())));
/// assert_eq!(to_digit("123"), Ok(("23", 1)))
/// ```
pub fn map_res<T, U, I, O>(parser: T, transform: U) -> impl Fn(I) -> KResult<I, O>
where
    I: Clone,
    U: Fn(I) -> O,
    T: Parser<I>,
{
    move |source| {
        //TODO: Remove unwrap when error management has been worked on
        let (suffix, prefix) = parser.parse(source).unwrap();
        let trans = transform(prefix.clone());

        Ok((suffix, trans))
    }
}

/// Checks if char is an ascii digit
pub fn is_digit(char: char) -> bool {
    char.is_ascii_digit()
}

/// Checks if char is an ascii alphabetic
pub fn is_alphabetic(char: char) -> bool {
    char.is_alphabetic()
}

/// Checks if char is an ascii alphanumeric
pub fn is_alphanumeric(char: char) -> bool {
    char.is_alphanumeric()
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
/// assert_eq!(parse("123max"), Ok(("max", "123")));
/// assert_eq!(parse("12max"), Ok(("max", "12")));
/// assert_eq!(parse("max123"), Ok(("max123", "")));
/// ```
pub fn take_while<F, I, C>(condition: F) -> impl Fn(I) -> KResult<I, I>
where
    I: InputTake + InputTakeAtPosition<Item = u8> + InputLength,
    C: From<u8>,
    F: Fn(C) -> bool,
{
    move |source| source.split_at_position(|e| !condition(e.into()))
}
/// Consume the input and slice
/// if it matches the predicate
/// but stop at the specified boundary
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use kombinator::{take_while_n, is_digit};
///
/// // Define the parsers
/// let parse = take_while_n(3, is_digit);
///
/// assert_eq!(parse("2000"), Ok(("0", "200")));
/// assert_eq!(parse("300"), Ok(("", "300")));
/// ```
pub fn take_while_n<F, I, C>(n: usize, condition: F) -> impl Fn(I) -> KResult<I, I>
where
    I: InputTake + InputTakeAtPosition<Item = u8> + InputLength,
    C: From<u8>,
    F: Fn(C) -> bool,
{
    move |source| source.split_at_bounded_position(n, |e| !condition(e.into()))
}

/// Combine two parsers together
/// and return the result of the first
/// parser that matches
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use kombinator::{either, tag, ParserError};
///
/// // Define the parsers
/// let either_tag = either(tag("1"), tag("2"));
///
/// assert_eq!(either_tag("12"), Ok(("2", "1")));
/// assert_eq!(either_tag("21"), Ok(("1", "2")));
/// assert_eq!(either_tag("3"), Err(ParserError::NoMatch));
/// ```
pub fn either<P1, P2, I>(p1: P1, p2: P2) -> impl Fn(I) -> KResult<I, I>
where
    I: Clone,
    P1: Parser<I>,
    P2: Parser<I>,
{
    move |source| p1.parse(source.clone()).or(p2.parse(source))
}
/// Sequence multiple parser together
/// and return the result of all the parsers
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use kombinator::{sequence, tag};
///
/// // Define the parsers
/// let sequence = sequence(tag("http"), tag("/"), tag("1"));
///
/// assert_eq!(sequence("http/1"), Ok(("", ("http", "/", "1"))))
/// ```
pub fn sequence<P1, P2, P3, I>(p1: P1, p2: P2, p3: P3) -> impl Fn(I) -> KResult<I, (I, I, I)>
where
    P1: Parser<I>,
    P2: Parser<I>,
    P3: Parser<I>,
{
    move |source| {
        let (input, res1) = p1.parse(source)?;
        let (input, res2) = p2.parse(input)?;
        let (input, res3) = p3.parse(input)?;

        Ok((input, (res1, res2, res3)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_test() {
        let parse_hashtag = tag("#");
        assert_eq!(parse_hashtag("#123"), Ok(("123", "#")));
        assert_eq!(parse_hashtag("#hello world"), Ok(("hello world", "#")));

        let parse_http = tag("http");

        assert_eq!(parse_http("httvp"), Err(ParserError::NoMatch));
        assert_eq!(parse_http("httpisking"), Ok(("isking", "http")));
    }

    #[test]
    fn take_while_test() {
        let parse = take_while(is_digit);

        assert_eq!(parse("123max"), Ok(("max", "123")));
        assert_eq!(parse("12max"), Ok(("max", "12")));
    }

    #[test]
    fn take_while_n_test() {
        let parse = take_while_n(3, is_digit);

        assert_eq!(parse("2000"), Ok(("0", "200")));
        assert_eq!(parse("300"), Ok(("", "300")));
    }

    #[test]
    fn map_res_test() {
        let parse_one = tag("1");
        let to_string = map_res(&parse_one, |suffix: &str| suffix.to_string());
        let to_digit = map_res(&parse_one, |suffix: &str| suffix.parse::<usize>().unwrap());

        assert_eq!(to_string("123"), Ok(("23", "1".to_string())));
        assert_eq!(to_digit("123"), Ok(("23", 1)))
    }

    #[test]
    fn either_test() {
        let either_tag = either(tag("1"), tag("2"));

        assert_eq!(either_tag("12"), Ok(("2", "1")));
        assert_eq!(either_tag("21"), Ok(("1", "2")));
    }

    #[test]
    fn sequence_test() {
        let sequence = sequence(tag("http"), either(tag("/"), tag("2")), tag("1"));
        assert_eq!(sequence("http/1"), Ok(("", ("http", "/", "1"))))
    }

    #[test]
    fn test_http_response_header() {
        let input = "HTTP/1.2 200 OK";

        let (input, http) = tag("HTTP/")(input).expect("This should work, this is a bug");
        let (input, number1) =
            take_while_n(1, is_digit)(input).expect("This should work, this is a bug");
        let (input, dot) = tag(".")(input).expect("This should work, this is a bug");
        let (input, number2) =
            take_while_n(1, is_digit)(input).expect("This should work, this is a bug");
        let (input, space) = tag(" ")(input).expect("This should work, this is a bug");
        let (input, two_hundred) =
            take_while_n(3, is_digit)(input).expect("This should work, this is a bug");
        let (input, space) = tag(" ")(input).expect("This should work, this is a bug");
        let (input, ok) = tag("OK")(input).expect("This should work, this is a bug");

        assert_eq!(http, "HTTP/");
        assert_eq!(number1, "1");
        assert_eq!(dot, ".");
        assert_eq!(number2, "2");
        assert_eq!(space, " ");
        assert_eq!(two_hundred, "200");
        assert_eq!(space, " ");
        assert_eq!(ok, "OK");
    }
}
