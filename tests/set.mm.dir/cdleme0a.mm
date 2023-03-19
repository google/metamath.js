include "lhpat2.mm"

theorem cdleme0a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme0.l: |- .<_ = ( le ` K )
  assume cdleme0.j: |- .\/ = ( join ` K )
  assume cdleme0.m: |- ./\ = ( meet ` K )
  assume cdleme0.a: |- A = ( Atoms ` K )
  assume cdleme0.h: |- H = ( LHyp ` K )
  assume cdleme0.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ P =/= Q ) ) -> U e. A )

  proof
    cA
    cP
    cQ
    cU
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
    cdleme0.u
    lhpat2
end
