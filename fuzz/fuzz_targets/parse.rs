#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else { return };
    if let Ok(tokens) = bil::lexer::tokenize(src) {
        let _ = bil::parser::Parser::new(tokens).parse_program();
    }
});
