include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "oveq2i.mm"
include "cdleme42a.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "syl5req.mm"

theorem cdleme42d
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme42.b: |- B = ( Base ` K )
  assume cdleme42.l: |- .<_ = ( le ` K )
  assume cdleme42.j: |- .\/ = ( join ` K )
  assume cdleme42.m: |- ./\ = ( meet ` K )
  assume cdleme42.a: |- A = ( Atoms ` K )
  assume cdleme42.h: |- H = ( LHyp ` K )
  assume cdleme42.v: |- V = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) -> ( R .\/ ( ( R .\/ V ) ./\ W ) ) = ( R .\/ V ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cR
    cV
    c.or
    co
    #
    cR
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    cR
    @1
    cW
    c.an
    co
    #
    c.or
    co
    cV
    @3
    cR
    c.or
    cdleme42.v
    oveq2i
    @0
    @3
    @4
    cR
    c.or
    @0
    @2
    @1
    cW
    c.an
    cA
    cB
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme42.b
    cdleme42.l
    cdleme42.j
    cdleme42.m
    cdleme42.a
    cdleme42.h
    cdleme42.v
    cdleme42a
    oveq1d
    oveq2d
    syl5req
end
