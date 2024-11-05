#![allow(dead_code, unused_variables)]

#[derive(Debug, PartialEq)]
enum ParserError {
    NoMatch,
}

type PResult<I, O, E = ParserError> = Result<(I, O), E>;

fn tag(pattern: &str) -> impl Fn(&[u8]) -> PResult<&str, &str> + '_ {
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

fn is_digit(char: char) -> bool {
    char.is_ascii_digit()
}

fn take_while_n<F>(n: usize, cond: F) -> impl Fn(&[u8]) -> PResult<&str, &str> {
    move |source| todo!("Implementing take_while_n")
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

    fn take_while_n_test() {
        let parse = take_while_n(2, is_digit);

        // assert_eq!(parse(b"max123"), Ok(("23", "max1")))
        // assert_eq!(parse(b"1max"), Ok(("23", "max1")))
    }

    #[test]
    fn test_http_response_header() {
        let input = "HTTP/1.x 200 OK";
        let (input, http) = tag("HTTP")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, slash) = tag("/")(input.as_bytes()).expect("This should work, this is a bug");
        let (input, slash) =
            take_while_n(1, is_digit)(input.as_bytes()).expect("This should work, this is a bug");

        assert_eq!(http, "HTTP");
        assert_eq!(slash, "/");
    }
}
