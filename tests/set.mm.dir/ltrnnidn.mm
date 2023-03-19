include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "ctrl.mm"
include "cfv.mm"
include "cp0.mm"
include "cal.mm"
include "simp1l.mm"
include "hlatl.mm"
include "syl.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "eqid.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "atn0.mm"
include "syl2anc.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpl2l.mm"
include "simpr.mm"
include "trl0.mm"
include "syl112anc.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem ltrnnidn
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume ltrnnidn.b: |- B = ( Base ` K )
  assume ltrnnidn.l: |- .<_ = ( le ` K )
  assume ltrnnidn.a: |- A = ( Atoms ` K )
  assume ltrnnidn.h: |- H = ( LHyp ` K )
  assume ltrnnidn.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( F ` P ) =/= P )

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
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    wne
    #
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cF
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cK
    cp0
    cfv
    #
    wne
    #
    cP
    cF
    cfv
    #
    cP
    wne
    @7
    cK
    cal
    wcel
    #
    @9
    cA
    wcel
    #
    @11
    @7
    @0
    @13
    @0
    @1
    @5
    @6
    simp1l
    cK
    hlatl
    syl
    @7
    @2
    @3
    @4
    @14
    @2
    @5
    @6
    simp1
    @2
    @3
    @4
    @6
    simp2l
    @2
    @3
    @4
    @6
    simp2r
    cA
    cB
    @8
    cT
    cF
    cH
    cK
    cW
    ltrnnidn.b
    ltrnnidn.a
    ltrnnidn.h
    ltrnnidn.t
    @8
    eqid
    #
    trlnidat
    syl3anc
    cA
    @9
    cK
    @10
    @10
    eqid
    #
    ltrnnidn.a
    atn0
    syl2anc
    @7
    @12
    cP
    @9
    @10
    @7
    @12
    cP
    wceq
    #
    @9
    @10
    wceq
    #
    @7
    @17
    wa
    @2
    @6
    @3
    @17
    @18
    @2
    @5
    @6
    @17
    simpl1
    @2
    @5
    @6
    @17
    simpl3
    @3
    @4
    @2
    @6
    @17
    simpl2l
    @7
    @17
    simpr
    cA
    cP
    @8
    cT
    cF
    cH
    cK
    c.le
    cW
    @10
    ltrnnidn.l
    @16
    ltrnnidn.a
    ltrnnidn.h
    ltrnnidn.t
    @15
    trl0
    syl112anc
    ex
    necon3d
    mpd
end
