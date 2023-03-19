include "cdleme9.mm"

theorem cdleme9tN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume cdleme9t.l: |- .<_ = ( le ` K )
  assume cdleme9t.j: |- .\/ = ( join ` K )
  assume cdleme9t.m: |- ./\ = ( meet ` K )
  assume cdleme9t.a: |- A = ( Atoms ` K )
  assume cdleme9t.h: |- H = ( LHyp ` K )
  assume cdleme9t.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme9t.g: |- F = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme9t.x: |- X = ( ( P .\/ T ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ ( T e. A /\ -. T .<_ W ) ) /\ -. T .<_ ( P .\/ Q ) ) -> ( F .\/ X ) = ( Q .\/ X ) )

  proof
    cA
    cX
    cP
    cQ
    cT
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme9t.l
    cdleme9t.j
    cdleme9t.m
    cdleme9t.a
    cdleme9t.h
    cdleme9t.u
    cdleme9t.g
    cdleme9t.x
    cdleme9
end
