include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "wss.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl3.mm"
include "simprr.mm"
include "dihord3.mm"
include "syl122anc.mm"
include "wn.mm"
include "dihord5a.mm"
include "dihord5b.mm"
include "impbida.mm"
include "dihord6a.mm"
include "dihord6b.mm"
include "dihord4.mm"
include "4casesdan.mm"

theorem dihord
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihord.b: |- B = ( Base ` K )
  assume dihord.l: |- .<_ = ( le ` K )
  assume dihord.h: |- H = ( LHyp ` K )
  assume dihord.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) -> ( ( I ` X ) C_ ( I ` Y ) <-> X .<_ Y ) )

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
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    #
    cY
    cW
    c.le
    wbr
    #
    cX
    cI
    cfv
    cY
    cI
    cfv
    wss
    #
    cX
    cY
    c.le
    wbr
    #
    wb
    #
    @3
    @4
    @5
    wa
    #
    wa
    @0
    @1
    @4
    @2
    @5
    @8
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @2
    @9
    simpl2
    @3
    @4
    @5
    simprl
    @0
    @1
    @2
    @9
    simpl3
    @3
    @4
    @5
    simprr
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    dihord.i
    dihord3
    syl122anc
    @3
    @4
    @5
    wn
    #
    wa
    #
    wa
    @0
    @1
    @4
    @2
    @10
    @8
    @0
    @1
    @2
    @11
    simpl1
    @0
    @1
    @2
    @11
    simpl2
    @3
    @4
    @10
    simprl
    @0
    @1
    @2
    @11
    simpl3
    @3
    @4
    @10
    simprr
    @0
    @1
    @4
    wa
    @2
    @10
    wa
    w3a
    @6
    @7
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    dihord.i
    dihord5a
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    dihord.i
    dihord5b
    impbida
    syl122anc
    @3
    @4
    wn
    #
    @5
    wa
    #
    wa
    @0
    @1
    @12
    @2
    @5
    @8
    @0
    @1
    @2
    @13
    simpl1
    @0
    @1
    @2
    @13
    simpl2
    @3
    @12
    @5
    simprl
    @0
    @1
    @2
    @13
    simpl3
    @3
    @12
    @5
    simprr
    @0
    @1
    @12
    wa
    @2
    @5
    wa
    w3a
    @6
    @7
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    dihord.i
    dihord6a
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    dihord.i
    dihord6b
    impbida
    syl122anc
    @3
    @12
    @10
    wa
    #
    wa
    @0
    @1
    @12
    @2
    @10
    @8
    @0
    @1
    @2
    @14
    simpl1
    @0
    @1
    @2
    @14
    simpl2
    @3
    @12
    @10
    simprl
    @0
    @1
    @2
    @14
    simpl3
    @3
    @12
    @10
    simprr
    cB
    cH
    cI
    cK
    c.le
    cW
    cX
    cY
    dihord.b
    dihord.l
    dihord.h
    dihord.i
    dihord4
    syl122anc
    4casesdan
end
