include "cdleme0c.mm"

theorem cdleme0gN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme0c.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ R e. A ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> V =/= Q )

  proof
    cA
    cP
    cR
    cQ
    cV
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme0.l
    cdleme0.j
    cdleme0.m
    cdleme0.a
    cdleme0.h
    cdleme0c.3
    cdleme0c
end
