include "cv.mm"
include "co.mm"
include "wbr.mm"
include "breq1.mm"
include "cdlemefrs29pre00.mm"

theorem cdlemefs29pre00N
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  assume cdlemefs29.b: |- B = ( Base ` K )
  assume cdlemefs29.l: |- .<_ = ( le ` K )
  assume cdlemefs29.j: |- .\/ = ( join ` K )
  assume cdlemefs29.m: |- ./\ = ( meet ` K )
  assume cdlemefs29.a: |- A = ( Atoms ` K )
  assume cdlemefs29.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ -. R .<_ W ) /\ R .<_ ( P .\/ Q ) ) /\ s e. A ) -> ( ( ( -. s .<_ W /\ s .<_ ( P .\/ Q ) ) /\ ( s .\/ ( R ./\ W ) ) = R ) <-> ( -. s .<_ W /\ ( s .\/ ( R ./\ W ) ) = R ) ) )

  proof
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    cR
    @1
    c.le
    wbr
    cA
    cB
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    cdlemefs29.b
    cdlemefs29.l
    cdlemefs29.j
    cdlemefs29.m
    cdlemefs29.a
    cdlemefs29.h
    @0
    cR
    @1
    c.le
    breq1
    cdlemefrs29pre00
end
