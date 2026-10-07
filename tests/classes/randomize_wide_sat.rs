//! §18 — `randomize()` of rand sets with a variable wider than 64 bits,
//! which go to the SAT path (#261): constraints on the wide variables
//! themselves, `dist` / `soft` / `solve ... before` / inline constraints in
//! such a set, sets that cannot be satisfied, and a bus-transaction item
//! with wide data and strobe arrays.
//!
//! Every program checks its own values in SystemVerilog and prints a line
//! the test reads; a failed check is reported as `bad=`.

use xezim::simulate;

fn lines(src: &str, tag: &str) -> Vec<String> {
    let sim = simulate(src, 1000).expect("sim");
    sim.output
        .iter()
        .filter(|o| o.message.starts_with(tag))
        .map(|o| o.message.clone())
        .collect()
}

/// The value of `key=` in `line`.
fn num(line: &str, key: &str) -> i64 {
    line.split_whitespace()
        .find_map(|t| t.strip_prefix(key))
        .unwrap_or_else(|| panic!("{key} in {line}"))
        .parse()
        .unwrap()
}

/// One line `R ok=<solved> bad=<violations> …` from `src`.
fn result(src: &str) -> String {
    let out = lines(src, "R ");
    assert_eq!(out.len(), 1, "{out:?}");
    out[0].clone()
}

// ----------------------------------------------------- wide constraint forms

/// Arithmetic, a multi-bit part-select and a mask on 128-bit variables, and
/// a relation between two of them.
#[test]
fn arithmetic_selects_and_masks_on_wide_variables() {
    let r = result(
        "class C;
  rand bit [127:0] a, b, c, d;
  constraint k {
    a + 1 == 128'h100;
    b[127:8] == 0;
    (c & 128'hff) == 0; c != 0;
    d == a + b; d[127:120] == 8'h0;
  }
endclass
module t; initial begin C o = new(); int ok, bad;
  repeat (8) begin
    if (o.randomize()) ok++; else bad++;
    if (o.a != 128'hff || o.b > 255 || o.c[7:0] != 0 || o.c == 0 || o.d != o.a + o.b) bad++;
  end
  $display(\"R ok=%0d bad=%0d\", ok, bad);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 8, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
}

/// 1024 bits: the width of the widest data bus.
#[test]
fn a_1024_bit_variable() {
    let r = result(
        "class C;
  rand bit [1023:0] d;
  constraint k { (d >> 64) == 0; d[3:0] == 4'h5; }
endclass
module t; initial begin C o = new(); int ok, bad; bit [63:0] lo, prev; int moved;
  repeat (8) begin
    if (o.randomize()) ok++; else bad++;
    if ((o.d >> 64) != 0 || o.d[3:0] != 4'h5) bad++;
    lo = o.d[63:0]; if (lo != prev) moved++; prev = lo;
  end
  $display(\"R ok=%0d bad=%0d moved=%0d\", ok, bad, moved);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 8, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
    assert!(num(&r, "moved=") >= 6, "the low bits should vary: {r}");
}

/// An inline constraint ties a wide variable to another.
#[test]
fn inline_constraints_on_wide_variables() {
    let r = result(
        "class C; rand bit [127:0] x, y; endclass
module t; initial begin C o = new(); int ok, bad;
  repeat (8) begin
    if (o.randomize() with { x == y + 1; y[127:64] == 64'h1; }) ok++; else bad++;
    if (o.x != o.y + 1 || o.y[127:64] != 64'h1) bad++;
  end
  $display(\"R ok=%0d bad=%0d\", ok, bad);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 8, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
}

/// §18.5.4: the weights of a `dist` hold in a set the SAT path solves.
#[test]
fn dist_weights_hold_with_a_wide_variable() {
    let r = result(
        "class C;
  rand bit [127:0] w;
  rand int n;
  constraint k { n dist {0 := 6, [1:3] :/ 3, [6:10] :/ 1}; (w >> 8) == n; }
endclass
module t; initial begin C o = new(); int ok, bad, z, s, l;
  repeat (400) begin
    if (o.randomize()) ok++; else bad++;
    if ((o.w >> 8) != o.n) bad++;
    if (o.n == 0) z++; else if (o.n <= 3) s++; else if (o.n >= 6 && o.n <= 10) l++; else bad++;
  end
  $display(\"R ok=%0d bad=%0d z=%0d s=%0d l=%0d\", ok, bad, z, s, l);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 400, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
    // 6 : 3 : 1 of 400 (240 / 120 / 40; sd ~10 / ~9 / ~6)
    assert!((200..=280).contains(&num(&r, "z=")), "{r}");
    assert!((85..=155).contains(&num(&r, "s=")), "{r}");
    assert!((18..=65).contains(&num(&r, "l=")), "{r}");
}

/// §18.5.14: a soft item gives way to a hard one, and holds otherwise.
#[test]
fn soft_items_with_a_wide_variable() {
    let r = result(
        "class C;
  rand bit [127:0] w;
  rand int x, y;
  constraint h { x > 10; (w >> 8) == 0; }
  constraint s { soft x == 5; soft y == 7; soft w == 128'h42; }
endclass
module t; initial begin C o = new(); int ok, bad;
  repeat (8) begin
    if (o.randomize()) ok++; else bad++;
    if (o.x <= 10 || o.y != 7 || o.w != 128'h42) bad++;
  end
  $display(\"R ok=%0d bad=%0d\", ok, bad);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 8, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
}

/// §18.5.10: with `solve s before w`, `s` is 1 half the time; without an
/// ordering the solutions are equally likely, and `s == 1` leaves a single
/// one (`w == 0`) against 2**128 for `s == 0`.
#[test]
fn solve_before_with_a_wide_variable() {
    let r = result(
        "class A; rand bit s; rand bit [127:0] w; constraint c { s -> w == 0; } endclass
class B; rand bit s; rand bit [127:0] w; constraint c { s -> w == 0; solve s before w; } endclass
module t; initial begin A a = new(); B b = new(); int ok, bad, sa, sb;
  repeat (400) begin
    if (a.randomize()) ok++; else bad++;
    if (b.randomize()) ok++; else bad++;
    if (a.s && a.w != 0 || b.s && b.w != 0) bad++;
    sa += a.s; sb += b.s;
  end
  $display(\"R ok=%0d bad=%0d sa=%0d sb=%0d\", ok, bad, sa, sb);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 800, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
    assert!(num(&r, "sa=") <= 4, "{r}");
    // 1/2 of 400 (sd 10)
    assert!((160..=240).contains(&num(&r, "sb=")), "{r}");
}

// ------------------------------------------------------------ unsatisfiable

/// §18.6.1 / §18.6.2: an unsatisfiable set fails, and the variables keep
/// their values. Each class has a wide variable, so the SAT path decides.
#[test]
fn unsatisfiable_sets_fail_and_keep_their_values() {
    for (name, decl) in [
        (
            "contradiction",
            "rand bit [127:0] a, x; constraint k { a < x; x < a; }",
        ),
        (
            "empty domain",
            "rand bit [127:0] x; constraint k { x < 5; x > 10; }",
        ),
        (
            "shift and bit",
            "rand bit [127:0] x; constraint k { (x >> 8) == 0; x[9] == 1; }",
        ),
        (
            "wide array elements",
            "rand bit [127:0] x; rand bit [127:0] e[]; \
             constraint k { e.size() == 4; foreach (e[i]) { (e[i] >> 8) == 0; e[i] > 300; } }",
        ),
        (
            "function of others",
            "rand bit [127:0] x; rand int y, z; \
             constraint k { y == 64; z == y / 8; z != 8; }",
        ),
        (
            "zero dist weights",
            "rand bit [127:0] x; rand int z; constraint k { z dist {0 := 0, [1:9] :/ 0}; }",
        ),
        (
            "dist ruled out",
            "rand bit [127:0] x; rand int z, y; \
             constraint k { z dist {0 := 6, [1:3] :/ 3}; z > y; y >= 3; }",
        ),
        (
            "array size conflict",
            "rand bit [127:0] x; rand bit [7:0] e[]; rand int n; \
             constraint k { e.size() == n; n == 5; e.size() == 6; }",
        ),
        (
            "elements after sizing",
            "rand bit [127:0] x; rand bit [7:0] e[]; \
             constraint k { e.size() == 3; foreach (e[i]) e[i] < e[0]; }",
        ),
        (
            "unique",
            "rand bit [127:0] x; rand int z[3]; \
             constraint k { foreach (z[i]) z[i] inside {[0:1]}; unique {z}; }",
        ),
    ] {
        let src = format!(
            "class C; {decl} endclass
module t; initial begin C o = new(); int r; bit [127:0] prev;
  o.x = 128'h1234_5678; prev = o.x;
  r = o.randomize();
  $display(\"R r=%0d kept=%0d\", r, o.x == prev);
end endmodule"
        );
        let r = result(&src);
        assert_eq!(num(&r, "r="), 0, "{name}: {r}");
        assert_eq!(num(&r, "kept="), 1, "{name}: {r}");
    }
}

/// §18.5.14: soft items that conflict with a hard one, or with each other,
/// never fail the call; the later soft item wins.
#[test]
fn soft_conflicts_never_fail() {
    let r = result(
        "class C;
  rand bit [127:0] w;
  rand int x;
  constraint h { x > 10; }
  constraint s1 { soft x == 5; }
  constraint s2 { soft x == 20; soft x == 30; }
endclass
module t; initial begin C o = new(); int ok, bad;
  repeat (4) begin
    if (o.randomize()) ok++; else bad++;
    if (o.x != 30) bad++;
  end
  $display(\"R ok=%0d bad=%0d\", ok, bad);
end endmodule",
    );
    assert_eq!(num(&r, "ok="), 4, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
}

// ---------------------------------------------------- a bus transaction item

/// The shape that motivated the SAT path: a bus item with 1024-bit data and
/// 128-bit strobes sized by the burst length, bounded through shifts by the
/// configured widths (state), per-beat delays under a `dist`, a soft
/// default, the 4 KB boundary rule (a product of two rand variables) and
/// an inline constraint.
const BUS_ITEM: &str = "
class cfg_c;
  int id_width = 8;
  int data_width = 64;
  int strobe_width = 8;
endclass
typedef enum { WRITE, READ } access_e;
class bus_item;
  cfg_c cfg = new();
  rand access_e access;
  rand bit [31:0] id;
  rand bit [63:0] address;
  rand int burst_length;
  rand int burst_size;
  rand bit [1023:0] data[];
  rand bit [127:0] strobe[];
  rand int delay[];
  rand bit need_response;
  constraint c_id { (id >> this.cfg.id_width) == 0; }
  constraint c_len { burst_length inside {[1:16]}; }
  constraint c_size { burst_size inside {1, 2, 4, 8}; (8 * burst_size) <= this.cfg.data_width; }
  constraint c_4kb { ((address & 64'('h1000 - burst_size)) + (burst_length * burst_size)) <= 4096; }
  constraint c_data {
    solve access, burst_length before data;
    (access == WRITE) -> data.size() == burst_length;
    (access == READ) -> data.size() == 0;
    foreach (data[i]) (data[i] >> this.cfg.data_width) == 0;
  }
  constraint c_strobe {
    solve access, burst_length before strobe;
    (access == WRITE) -> strobe.size() == burst_length;
    (access == READ) -> strobe.size() == 0;
    foreach (strobe[i]) (strobe[i] >> this.cfg.strobe_width) == 0;
  }
  constraint c_delay {
    delay.size() == burst_length;
    foreach (delay[i]) delay[i] dist {0 := 6, [1:3] :/ 3, [6:10] :/ 1};
  }
  constraint c_need { soft need_response == 0; }
endclass
";

#[test]
fn bus_write_item() {
    let src = format!(
        "{BUS_ITEM}
module t; initial begin bus_item it = new(); int ok, bad, z, s, l, n; bit [63:0] lo;
  for (int k = 0; k < 20; k++) begin
    if (it.randomize() with {{
          access == WRITE;
          address >= 64'h0001_0000_0000_0000 * 3;
          address <= 64'h0001_0000_0000_0000 * 4 - 1;
        }}) ok++; else bad++;
    if (it.access != WRITE || it.id > 255 || it.need_response != 0) bad++;
    if (it.address < 64'h0003_0000_0000_0000 || it.address > 64'h0003_ffff_ffff_ffff) bad++;
    if (it.burst_length < 1 || it.burst_length > 16 || !(it.burst_size inside {{1, 2, 4, 8}})) bad++;
    if ((it.address & 64'('h1000 - it.burst_size)) + it.burst_length * it.burst_size > 4096) bad++;
    if (it.data.size() != it.burst_length || it.strobe.size() != it.burst_length) bad++;
    if (it.delay.size() != it.burst_length) bad++;
    foreach (it.data[i]) if ((it.data[i] >> 64) != 0) bad++;
    foreach (it.strobe[i]) if ((it.strobe[i] >> 8) != 0) bad++;
    foreach (it.delay[i]) begin
      n++;
      if (it.delay[i] == 0) z++; else if (it.delay[i] <= 3) s++;
      else if (it.delay[i] >= 6 && it.delay[i] <= 10) l++; else bad++;
    end
  end
  $display(\"R ok=%0d bad=%0d n=%0d z=%0d s=%0d l=%0d\", ok, bad, n, z, s, l);
end endmodule"
    );
    let r = result(&src);
    assert_eq!(num(&r, "ok="), 20, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
    // 6 : 3 : 1 over every beat
    let n = num(&r, "n=") as f64;
    let share = |k: &str| num(&r, k) as f64 / n;
    assert!(n >= 40.0, "{r}");
    assert!((0.45..=0.75).contains(&share("z=")), "{r}");
    assert!((0.15..=0.45).contains(&share("s=")), "{r}");
    assert!(share("l=") <= 0.25, "{r}");
}

/// The read side: the data and strobe arrays are sized to zero, and a
/// response array of a 2-bit enum is weighted by state weights.
#[test]
fn bus_read_response() {
    let src = "
typedef enum bit [1:0] { OKAY, EXOKAY, SLVERR, DECERR } resp_e;
class resp_item;
  int burst_length = 16;
  int w_okay = 6, w_exokay = 2, w_slverr = 1, w_decerr = 1;
  rand bit [1023:0] data[];
  rand resp_e response[];
  constraint c_data { data.size() == burst_length; foreach (data[i]) (data[i] >> 64) == 0; }
  constraint c_resp {
    response.size() == burst_length;
    foreach (response[i]) response[i] dist {
      OKAY := w_okay, EXOKAY := w_exokay, SLVERR := w_slverr, DECERR := w_decerr
    };
  }
endclass
module t; initial begin resp_item it = new(); int ok, bad, cnt[4];
  repeat (25) begin
    if (it.randomize()) ok++; else bad++;
    if (it.data.size() != 16 || it.response.size() != 16) bad++;
    foreach (it.data[i]) if ((it.data[i] >> 64) != 0) bad++;
    foreach (it.response[i]) cnt[it.response[i]]++;
  end
  $display(\"R ok=%0d bad=%0d c0=%0d c1=%0d c2=%0d c3=%0d\", ok, bad, cnt[0], cnt[1], cnt[2], cnt[3]);
end endmodule";
    let r = result(src);
    assert_eq!(num(&r, "ok="), 25, "{r}");
    assert_eq!(num(&r, "bad="), 0, "{r}");
    // 6 : 2 : 1 : 1 of 400 (240 / 80 / 40 / 40)
    assert!((195..=285).contains(&num(&r, "c0=")), "{r}");
    assert!((50..=110).contains(&num(&r, "c1=")), "{r}");
    assert!((18..=65).contains(&num(&r, "c2=")), "{r}");
    assert!((18..=65).contains(&num(&r, "c3=")), "{r}");
}
