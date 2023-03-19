include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wss.mm"
include "simp2r.mm"
include "simp3r.mm"
include "clat.mm"
include "wi.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "mtod.mm"
include "pm2.21d.mm"
include "imp.mm"

theorem dihord6b
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vr: setvar r
  assume dihord3.b: |- B = ( Base ` K )
  assume dihord3.l: |- .<_ = ( le ` K )
  assume dihord3.h: |- H = ( LHyp ` K )
  assume dihord3.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ Y .<_ W ) ) /\ X .<_ Y ) -> ( I ` X ) C_ ( I ` Y ) )

  proof
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
    wn
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
    @10
    @11
    @12
    @10
    @11
    @4
    @2
    @3
    @5
    @9
    simp2r
    @10
    @11
    @8
    @4
    @2
    @6
    @7
    @8
    simp3r
    @10
    cK
    clat
    wcel
    #
    @3
    @7
    cW
    cB
    wcel
    #
    @11
    @8
    wa
    @4
    wi
    @10
    @0
    @13
    @0
    @1
    @6
    @9
    simp1l
    cK
    hllat
    syl
    @2
    @3
    @5
    @9
    simp2l
    @2
    @6
    @7
    @8
    simp3l
    @10
    @1
    @14
    @0
    @1
    @6
    @9
    simp1r
    cB
    cH
    cK
    cW
    dihord3.b
    dihord3.h
    lhpbase
    syl
    cB
    cK
    c.le
    cX
    cY
    cW
    dihord3.b
    dihord3.l
    lattr
    syl13anc
    mpan2d
    mtod
    pm2.21d
    imp
end
