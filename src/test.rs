use crate::{interpret::Runtime, num::Num, value::Value};

#[test]
fn and_or() {
    let mut rt = Runtime::new();
    assert_eq!(Value::Num(Num::Int(2)), rt.eval("1 and 2 or 3").unwrap());
    assert_eq!(
        Value::Num(Num::Int(3)),
        rt.eval("1 < 2 and 3 or 4").unwrap()
    );
    assert_eq!(
        Value::Num(Num::Int(4)),
        rt.eval("1 > 2 and 3 or 4").unwrap()
    );
}
