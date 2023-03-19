include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "eqss.mm"
include "cple.mm"
include "wbr.mm"
include "eqid.mm"
include "dihord.mm"
include "wb.mm"
include "3com23.mm"
include "anbi12d.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "latasymb.mm"
include "syld3an1.mm"
include "bitrd.mm"
include "syl5bb.mm"

theorem dih11
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dih11.b: |- B = ( Base ` K )
  assume dih11.h: |- H = ( LHyp ` K )
  assume dih11.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) -> ( ( I ` X ) = ( I ` Y ) <-> X = Y ) )

  proof
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    wceq
    @0
    @1
    wss
    #
    @1
    @0
    wss
    #
    wa
    #
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
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
    wceq
    #
    @0
    @1
    eqss
    @10
    @4
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
    @12
    wbr
    #
    wa
    #
    @11
    @10
    @2
    @13
    @3
    @14
    cB
    cH
    cI
    cK
    @12
    cW
    cX
    cY
    dih11.b
    @12
    eqid
    #
    dih11.h
    dih11.i
    dihord
    @7
    @9
    @8
    @3
    @14
    wb
    cB
    cH
    cI
    cK
    @12
    cW
    cY
    cX
    dih11.b
    @16
    dih11.h
    dih11.i
    dihord
    3com23
    anbi12d
    cK
    clat
    wcel
    #
    @8
    @7
    @9
    @15
    @11
    wb
    @10
    @5
    @17
    @5
    @6
    @8
    @9
    simp1l
    cK
    hllat
    syl
    cB
    cK
    @12
    cX
    cY
    dih11.b
    @16
    latasymb
    syld3an1
    bitrd
    syl5bb
end
