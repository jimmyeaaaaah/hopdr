use crate::solver::util;
use std::time::Duration;
use tempfile::NamedTempFile;

pub(super) fn save_prog(prog: String) -> NamedTempFile {
    util::save_to_file(prog)
}
pub fn do_format(input: &str) -> String {
    // ocamlformat  --impl -
    let args = vec!["--impl", "-"];
    debug!("filename: {}", &args[0]);
    let out = util::exec_input_with_timeout(
        "ocamlformat",
        &args,
        input.as_bytes(),
        Duration::from_secs(1),
    );
    let s = String::from_utf8(out).unwrap();
    debug!("result: {s}");
    s
}

#[test]
fn test_do_format() {
    let s =
        "let rec fold_left f acc xs =match xs with[] -> acc  | x::xs' -> fold_left f (f acc x) xs'";
    let r = "let rec fold_left f acc xs =
  match xs with [] -> acc | x :: xs' -> fold_left f (f acc x) xs'\n";
    let r2 = do_format(s);
    assert_eq!(r, &r2);
}
