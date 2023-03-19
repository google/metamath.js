include "cdleme9a.mm"

theorem cdleme9taN
  let cA: class A
  let cP: class P
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume cdleme8t.l: |- .<_ = ( le ` K )
  assume cdleme8t.j: |- .\/ = ( join ` K )
  assume cdleme8t.m: |- ./\ = ( meet ` K )
  assume cdleme8t.a: |- A = ( Atoms ` K )
  assume cdleme8t.h: |- H = ( LHyp ` K )
  assume cdleme8t.x: |- X = ( ( P .\/ T ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( T e. A /\ P =/= T ) ) -> X e. A )

  proof
    cA
    cX
    cP
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme8t.l
    cdleme8t.j
    cdleme8t.m
    cdleme8t.a
    cdleme8t.h
    cdleme8t.x
    cdleme9a
end
