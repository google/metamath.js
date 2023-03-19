include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "cdib.mm"
include "wceq.mm"
include "eqid.mm"
include "dihvalb.mm"
include "3adant3.mm"
include "3adant2.mm"
include "sseq12d.mm"
include "dibord.mm"
include "bitrd.mm"

theorem dihord3
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihord3.b: |- B = ( Base ` K )
  assume dihord3.l: |- .<_ = ( le ` K )
  assume dihord3.h: |- H = ( LHyp ` K )
  assume dihord3.i: |- I = ( ( DIsoH ` K ) ` W )


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
    cX
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    cY
    @6
    cfv
    #
    wss
    cX
    cY
    c.le
    wbr
    @3
    @4
    @7
    @5
    @8
    @0
    @1
    @4
    @7
    wceq
    @2
    cB
    @6
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    dihord3.b
    dihord3.l
    dihord3.h
    dihord3.i
    @6
    eqid
    #
    dihvalb
    3adant3
    @0
    @2
    @5
    @8
    wceq
    @1
    cB
    @6
    cH
    cI
    cK
    c.le
    chlt
    cW
    cY
    dihord3.b
    dihord3.l
    dihord3.h
    dihord3.i
    @9
    dihvalb
    3adant2
    sseq12d
    cB
    cH
    @6
    cK
    c.le
    cW
    cX
    cY
    dihord3.b
    dihord3.l
    dihord3.h
    @9
    dibord
    bitrd
end
