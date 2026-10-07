//! §18.5 — `(x >> k) == c` and `(x & m) == c` in a class whose rand set
//! the joint solver does not take (#261).
//!
//! A rand variable wider than 64 bits anywhere in the class keeps the class
//! off the joint solver, which is where shifts are modelled (#229). The
//! per-variable trials then only re-drew `x`, and a 32-bit draw satisfies
//! `(x >> 8) == 0` with probability 2**-24, so `randomize()` returned 0.
//!
//! These tests assert the drawn VALUES satisfy the constraint, not merely
//! that `randomize()` returned 1.

use xezim::simulate;

fn lines(src: &str, tag: &str) -> Vec<String> {
    let sim = simulate(src, 1000).expect("sim");
    sim.output
        .iter()
        .filter(|o| o.message.starts_with(tag))
        .map(|o| o.message.clone())
        .collect()
}

/// Randomize `reps` times; each line is `R r=<ok> v=<hex value of expr>`.
fn draws(decl: &str, expr: &str, reps: usize) -> Vec<(i64, u128)> {
    let src = format!(
        "{decl}\n\
module t; initial begin C c=new();\n\
  for (int n=0;n<{reps};n++) begin\n\
    int r=c.randomize();\n\
    $display(\"R r=%0d v=%0h\", r, {expr});\n\
  end $finish; end endmodule"
    );
    lines(&src, "R ")
        .iter()
        .map(|l| {
            let mut it = l.split_whitespace().skip(1);
            let r: i64 = it.next().unwrap()[2..].parse().unwrap();
            let v = u128::from_str_radix(&it.next().unwrap()[2..], 16).unwrap();
            (r, v)
        })
        .collect()
}

fn spread(d: &[(i64, u128)]) -> usize {
    d.iter()
        .map(|x| x.1)
        .collect::<std::collections::HashSet<_>>()
        .len()
}

#[test]
fn shr_eq_zero_with_wide_sibling() {
    let d = draws(
        "class C; rand bit[31:0] x; rand bit[64:0] y; \
         constraint k { (x >> 8) == 0; } endclass",
        "c.x",
        16,
    );
    assert_eq!(d.len(), 16);
    for (r, v) in &d {
        assert_eq!(*r, 1, "(x >> 8) == 0 must solve");
        assert!(*v < 0x100, "x={v:x} violates (x >> 8) == 0");
    }
    assert!(spread(&d) > 1, "x should spread over 0..'hff, got {d:?}");
}

#[test]
fn shr_eq_nonzero_with_wide_sibling() {
    // (x >> 8) == 3  <=>  'h300 <= x <= 'h3ff
    let d = draws(
        "class C; rand bit[31:0] x; rand bit[64:0] y; \
         constraint k { (x >> 8) == 3; } endclass",
        "c.x",
        16,
    );
    for (r, v) in &d {
        assert_eq!(*r, 1, "(x >> 8) == 3 must solve");
        assert!(
            (0x300..=0x3ff).contains(v),
            "x={v:x} is outside 'h300..'h3ff"
        );
    }
}

#[test]
fn shr_by_member_width_with_wide_sibling() {
    // The shift amount read through a configuration handle.
    let d = draws(
        "class W; int w = 8; endclass\n\
         class C; W cfg = new(); rand logic[31:0] x; rand logic[127:0] y; \
         constraint k { (x >> this.cfg.w) == 0; } endclass",
        "c.x",
        16,
    );
    for (r, v) in &d {
        assert_eq!(*r, 1, "(x >> cfg.w) == 0 must solve");
        assert!(*v < 0x100, "x={v:x} violates (x >> 8) == 0");
    }
}

#[test]
fn mask_eq_with_wide_sibling() {
    let d = draws(
        "class C; rand bit[31:0] x; rand bit[64:0] y; \
         constraint k { (x & 32'hffff_ff00) == 32'h0000_1200; } endclass",
        "c.x",
        16,
    );
    for (r, v) in &d {
        assert_eq!(*r, 1, "(x & 'hffff_ff00) == 'h1200 must solve");
        assert!(
            (0x1200..=0x12ff).contains(v),
            "x={v:x} is outside 'h1200..'h12ff"
        );
    }
    assert!(
        spread(&d) > 1,
        "the unmasked bits should stay random, got {d:?}"
    );
}

#[test]
fn shr_eq_zero_on_the_wide_variable() {
    let d = draws(
        "class C; rand bit[127:0] x; constraint k { (x >> 8) == 0; } endclass",
        "c.x",
        16,
    );
    for (r, v) in &d {
        assert_eq!(*r, 1, "(x >> 8) == 0 must solve on a 128-bit x");
        assert!(*v < 0x100, "x={v:x} violates (x >> 8) == 0");
    }
    assert!(spread(&d) > 1, "x should spread over 0..'hff, got {d:?}");
}

#[test]
fn shr_eq_zero_on_wide_array_elements() {
    let src = "class C; rand bit[127:0] s[]; \
               constraint k { s.size() == 4; foreach (s[i]) { (s[i] >> 8) == 0; } } endclass\n\
module t; initial begin C c=new();\n\
  for (int n=0;n<8;n++) begin\n\
    int r=c.randomize();\n\
    $display(\"R r=%0d n=%0d %0h %0h %0h %0h\", r, c.s.size(), c.s[0], c.s[1], c.s[2], c.s[3]);\n\
  end $finish; end endmodule";
    let out = lines(src, "R ");
    assert_eq!(out.len(), 8);
    for l in &out {
        let f: Vec<&str> = l.split_whitespace().collect();
        assert_eq!(f[1], "r=1", "{l}");
        assert_eq!(f[2], "n=4", "{l}");
        for e in &f[3..7] {
            let v = u128::from_str_radix(e, 16).unwrap();
            assert!(v < 0x100, "element {v:x} violates (s[i] >> 8) == 0: {l}");
        }
    }
}

// Overflow. §11.6 computes `+`, `-`, `*` and `<<` at the context width,
// so a solution that holds only modulo 2**w satisfies the constraint, and
// this path may return one. The interval CSP and the trial loop of the
// other paths reason with exact integers and never return such a solution
// (with only wrapped solutions left, `randomize()` fails there).

/// `(x << 2) == 16` at 32 bits: any `x` whose low 30 bits are 4.
#[test]
fn left_shift_is_computed_at_the_context_width() {
    let d = draws(
        "class C; rand bit[31:0] x; rand bit[64:0] y; \
         constraint k { (x << 2) == 16; } endclass",
        "c.x",
        16,
    );
    for (r, v) in &d {
        assert_eq!(*r, 1, "(x << 2) == 16 must solve");
        assert_eq!(
            (v << 2) & 0xffff_ffff,
            16,
            "x={v:x} violates (x << 2) == 16"
        );
    }
}

/// `a + b == 50` at 32 bits: the sum modulo 2**32 is 50.
#[test]
fn sum_is_computed_at_the_context_width() {
    let src = "class C; rand bit[31:0] a, b; rand bit[64:0] y; \
               constraint k { a + b == 50; } endclass\n\
module t; initial begin C c=new();\n\
  for (int n=0;n<16;n++) begin\n\
    int r=c.randomize();\n\
    $display(\"R r=%0d a=%0d b=%0d\", r, c.a, c.b);\n\
  end $finish; end endmodule";
    let out = lines(src, "R ");
    assert_eq!(out.len(), 16);
    let mut seen = std::collections::HashSet::new();
    for l in &out {
        let f: Vec<&str> = l.split_whitespace().collect();
        assert_eq!(f[1], "r=1", "{l}");
        let a: u64 = f[2][2..].parse().unwrap();
        let b: u64 = f[3][2..].parse().unwrap();
        assert_eq!((a + b) & 0xffff_ffff, 50, "{l}");
        seen.insert(a);
    }
    assert!(seen.len() > 1, "a should vary: {out:?}");
}

/// `x * 4 == 40` for a signed `int`: `x` is 10 modulo 2**30.
#[test]
fn product_is_computed_at_the_context_width() {
    let d = draws(
        "class C; rand int x; rand bit[64:0] y; \
         constraint k { x * 4 == 40; } endclass",
        "c.x",
        16,
    );
    for (r, v) in &d {
        assert_eq!(*r, 1, "x * 4 == 40 must solve");
        assert_eq!((v * 4) & 0xffff_ffff, 40, "x={v:x} violates x * 4 == 40");
    }
}

/// With only wrapped solutions, `randomize()` still succeeds (§11.6), and
/// the value meets the constraint at the context width. (`a - b == 3`
/// would be computed at 32 bits, the width of `3`, where it has no
/// solution with `b >= 253`; `8'd3` keeps the context at 8 bits.)
#[test]
fn only_wrapped_solutions_still_solve() {
    let src = "class C; rand bit[7:0] a, b; rand bit[31:0] x; rand bit[64:0] y; \
               constraint k { a - b == 8'd3; b >= 253; (x << 2) == 16; x > 100; } endclass\n\
module t; initial begin C c=new();\n\
  for (int n=0;n<8;n++) begin\n\
    int r=c.randomize();\n\
    $display(\"R r=%0d a=%0d b=%0d x=%0d\", r, c.a, c.b, c.x);\n\
  end $finish; end endmodule";
    let out = lines(src, "R ");
    assert_eq!(out.len(), 8);
    for l in &out {
        let f: Vec<&str> = l.split_whitespace().collect();
        assert_eq!(f[1], "r=1", "{l}");
        let a: u64 = f[2][2..].parse().unwrap();
        let b: u64 = f[3][2..].parse().unwrap();
        let x: u64 = f[4][2..].parse().unwrap();
        assert_eq!((a + 256 - b) & 0xff, 3, "{l}");
        assert!(b >= 253 && x > 100, "{l}");
        assert_eq!((x << 2) & 0xffff_ffff, 16, "{l}");
    }
}
