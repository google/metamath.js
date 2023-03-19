include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "cxp.mm"
include "cin.mm"
include "breqi.mm"
include "wb.mm"
include "simp2.mm"
include "simp3.mm"
include "brxp.mm"
include "sylanbrc.mm"
include "brin.mm"
include "rbaib.mm"
include "syl.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "eqid.mm"
include "posasymb.mm"
include "bitrd.mm"

theorem posrasymb
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume posrasymb.b: |- B = ( Base ` K )
  assume posrasymb.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( ( K e. Poset /\ X e. B /\ Y e. B ) -> ( ( X .<_ Y /\ Y .<_ X ) <-> X = Y ) )

  proof
    cK
    cpo
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wa
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    #
    cY
    cX
    @6
    wbr
    #
    wa
    cX
    cY
    wceq
    @3
    @4
    @7
    @5
    @8
    @4
    cX
    cY
    @6
    cB
    cB
    cxp
    #
    cin
    #
    wbr
    #
    @3
    @7
    cX
    cY
    c.le
    @10
    posrasymb.l
    breqi
    @3
    cX
    cY
    @9
    wbr
    #
    @11
    @7
    wb
    @3
    @1
    @2
    @12
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    cX
    cY
    cB
    cB
    brxp
    sylanbrc
    @11
    @7
    @12
    cX
    cY
    @6
    @9
    brin
    rbaib
    syl
    syl5bb
    @5
    cY
    cX
    @10
    wbr
    #
    @3
    @8
    cY
    cX
    c.le
    @10
    posrasymb.l
    breqi
    @3
    cY
    cX
    @9
    wbr
    #
    @15
    @8
    wb
    @3
    @2
    @1
    @16
    @14
    @13
    cY
    cX
    cB
    cB
    brxp
    sylanbrc
    @15
    @8
    @16
    cY
    cX
    @6
    @9
    brin
    rbaib
    syl
    syl5bb
    anbi12d
    cB
    cK
    @6
    cX
    cY
    posrasymb.b
    @6
    eqid
    posasymb
    bitrd
end
