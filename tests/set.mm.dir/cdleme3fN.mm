include "cdleme0e.mm"

theorem cdleme3fN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme3.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> U =/= V )

  proof
    cA
    cP
    cQ
    cR
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme3.3
    cdleme0e
end
