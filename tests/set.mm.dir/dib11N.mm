include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "wbr.mm"
include "w3a.mm"
include "eqss.mm"
include "dibord.mm"
include "wb.mm"
include "3com23.mm"
include "anbi12d.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp3l.mm"
include "latasymb.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "syl5bb.mm"

theorem dib11N
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume dib11.b: |- B = ( Base ` K )
  assume dib11.l: |- .<_ = ( le ` K )
  assume dib11.h: |- H = ( LHyp ` K )
  assume dib11.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) -> ( ( I ` X ) = ( I ` Y ) <-> X = Y ) )

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
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    cY
    cB
    wcel
    #
    cY
    cW
    c.le
    wbr
    #
    wa
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
    @14
    @4
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
    #
    @15
    @14
    @2
    @16
    @3
    @17
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dib11.b
    dib11.l
    dib11.h
    dib11.i
    dibord
    @7
    @13
    @10
    @3
    @17
    wb
    cB
    cH
    cI
    cK
    c.le
    cW
    cY
    cX
    dib11.b
    dib11.l
    dib11.h
    dib11.i
    dibord
    3com23
    anbi12d
    @14
    cK
    clat
    wcel
    #
    @8
    @11
    @18
    @15
    wb
    @14
    @5
    @19
    @5
    @6
    @10
    @13
    simp1l
    cK
    hllat
    syl
    @7
    @8
    @9
    @13
    simp2l
    @7
    @10
    @11
    @12
    simp3l
    cB
    cK
    c.le
    cX
    cY
    dib11.b
    dib11.l
    latasymb
    syl3anc
    bitrd
    syl5bb
end
