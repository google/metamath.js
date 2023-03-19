include "lhpat2.mm"

theorem cdleme9a
  let cA: class A
  let cC: class C
  let cP: class P
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme8.l: |- .<_ = ( le ` K )
  assume cdleme8.j: |- .\/ = ( join ` K )
  assume cdleme8.m: |- ./\ = ( meet ` K )
  assume cdleme8.a: |- A = ( Atoms ` K )
  assume cdleme8.h: |- H = ( LHyp ` K )
  assume cdleme8.4: |- C = ( ( P .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( S e. A /\ P =/= S ) ) -> C e. A )

  proof
    cA
    cP
    cS
    cC
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme8.l
    cdleme8.j
    cdleme8.m
    cdleme8.a
    cdleme8.h
    cdleme8.4
    lhpat2
end
