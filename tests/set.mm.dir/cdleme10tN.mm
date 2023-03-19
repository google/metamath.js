include "cdleme10.mm"

theorem cdleme10tN
  let cA: class A
  let cR: class R
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  assume cdleme10t.l: |- .<_ = ( le ` K )
  assume cdleme10t.j: |- .\/ = ( join ` K )
  assume cdleme10t.m: |- ./\ = ( meet ` K )
  assume cdleme10t.a: |- A = ( Atoms ` K )
  assume cdleme10t.h: |- H = ( LHyp ` K )
  assume cdleme10t.y: |- Y = ( ( R .\/ T ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ R e. A /\ ( T e. A /\ -. T .<_ W ) ) -> ( T .\/ Y ) = ( T .\/ R ) )

  proof
    cA
    cY
    cR
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme10t.l
    cdleme10t.j
    cdleme10t.m
    cdleme10t.a
    cdleme10t.h
    cdleme10t.y
    cdleme10
end
