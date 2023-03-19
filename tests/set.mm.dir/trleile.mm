include "ctos.mm"
include "wcel.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wo.mm"
include "eqid.mm"
include "tleile.mm"
include "wb.mm"
include "wa.mm"
include "3simpc.mm"
include "brxp.mm"
include "sylibr.mm"
include "brin.mm"
include "rbaib.mm"
include "syl.mm"
include "ancomd.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "breqi.mm"
include "orbi12i.mm"

theorem trleile
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume trleile.b: |- B = ( Base ` K )
  assume trleile.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( ( K e. Toset /\ X e. B /\ Y e. B ) -> ( X .<_ Y \/ Y .<_ X ) )

  proof
    cK
    ctos
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
    cK
    cple
    cfv
    #
    cB
    cB
    cxp
    #
    cin
    #
    wbr
    #
    cY
    cX
    @6
    wbr
    #
    wo
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
    wo
    @3
    @9
    cX
    cY
    @4
    wbr
    #
    cY
    cX
    @4
    wbr
    #
    wo
    cB
    cK
    @4
    cX
    cY
    trleile.b
    @4
    eqid
    tleile
    @3
    @7
    @12
    @8
    @13
    @3
    cX
    cY
    @5
    wbr
    #
    @7
    @12
    wb
    @3
    @1
    @2
    wa
    @14
    @0
    @1
    @2
    3simpc
    #
    cX
    cY
    cB
    cB
    brxp
    sylibr
    @7
    @12
    @14
    cX
    cY
    @4
    @5
    brin
    rbaib
    syl
    @3
    cY
    cX
    @5
    wbr
    #
    @8
    @13
    wb
    @3
    @2
    @1
    wa
    @16
    @3
    @1
    @2
    @15
    ancomd
    cY
    cX
    cB
    cB
    brxp
    sylibr
    @8
    @13
    @16
    cY
    cX
    @4
    @5
    brin
    rbaib
    syl
    orbi12d
    mpbird
    @10
    @7
    @11
    @8
    cX
    cY
    c.le
    @6
    trleile.l
    breqi
    cY
    cX
    c.le
    @6
    trleile.l
    breqi
    orbi12i
    sylibr
end
