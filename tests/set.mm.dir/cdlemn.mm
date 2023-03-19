include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wss.mm"
include "cdlemn5.mm"
include "3expia.mm"
include "cdlemn11.mm"
include "impbid.mm"

theorem cdlemn
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vh: setvar h
  assume cdlemn11.b: |- B = ( Base ` K )
  assume cdlemn11.l: |- .<_ = ( le ` K )
  assume cdlemn11.j: |- .\/ = ( join ` K )
  assume cdlemn11.a: |- A = ( Atoms ` K )
  assume cdlemn11.h: |- H = ( LHyp ` K )
  assume cdlemn11.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn11.J: |- J = ( ( DIsoC ` K ) ` W )
  assume cdlemn11.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn11.s: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) /\ ( X e. B /\ X .<_ W ) ) ) -> ( R .<_ ( Q .\/ X ) <-> ( J ` R ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
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
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    w3a
    #
    wa
    cR
    cQ
    cX
    c.or
    co
    c.le
    wbr
    #
    cR
    cJ
    cfv
    cQ
    cJ
    cfv
    cX
    cI
    cfv
    c.po
    co
    wss
    #
    @0
    @1
    @2
    @3
    cA
    cB
    c.po
    cQ
    cR
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cW
    cX
    cdlemn11.b
    cdlemn11.l
    cdlemn11.j
    cdlemn11.a
    cdlemn11.h
    cdlemn11.u
    cdlemn11.s
    cdlemn11.i
    cdlemn11.J
    cdlemn5
    3expia
    @0
    @1
    @3
    @2
    cA
    cB
    c.po
    cQ
    cR
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cW
    cX
    cdlemn11.b
    cdlemn11.l
    cdlemn11.j
    cdlemn11.a
    cdlemn11.h
    cdlemn11.i
    cdlemn11.J
    cdlemn11.u
    cdlemn11.s
    cdlemn11
    3expia
    impbid
end
