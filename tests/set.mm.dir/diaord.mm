include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "ctrl.mm"
include "cltrn.mm"
include "crab.mm"
include "wceq.mm"
include "eqid.mm"
include "diaval.mm"
include "3adant3.mm"
include "3adant2.mm"
include "sseq12d.mm"
include "wi.mm"
include "wral.mm"
include "catm.mm"
include "trlord.mm"
include "ss2rab.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem diaord
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume dia11.b: |- B = ( Base ` K )
  assume dia11.l: |- .<_ = ( le ` K )
  assume dia11.h: |- H = ( LHyp ` K )
  assume dia11.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) -> ( ( I ` X ) C_ ( I ` Y ) <-> X .<_ Y ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    cY
    cB
    wcel
    cY
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    wss
    vf
    cv
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cX
    c.le
    wbr
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crab
    #
    @7
    cY
    c.le
    wbr
    #
    vf
    @9
    crab
    #
    wss
    #
    cX
    cY
    c.le
    wbr
    #
    @3
    @4
    @10
    @5
    @12
    @0
    @1
    @4
    @10
    wceq
    @2
    cB
    @6
    @9
    vf
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dia11.b
    dia11.l
    dia11.h
    @9
    eqid
    #
    @6
    eqid
    #
    dia11.i
    diaval
    3adant3
    @0
    @2
    @5
    @12
    wceq
    @1
    cB
    @6
    @9
    vf
    cH
    cI
    cK
    c.le
    chlt
    cW
    cY
    dia11.b
    dia11.l
    dia11.h
    @15
    @16
    dia11.i
    diaval
    3adant2
    sseq12d
    @3
    @14
    @8
    @11
    wi
    vf
    @9
    wral
    @13
    cK
    catm
    cfv
    #
    cB
    @6
    @9
    vf
    cH
    cK
    c.le
    cW
    cX
    cY
    dia11.b
    dia11.l
    @17
    eqid
    dia11.h
    @15
    @16
    trlord
    @8
    @11
    vf
    @9
    ss2rab
    syl6rbbr
    bitrd
end
