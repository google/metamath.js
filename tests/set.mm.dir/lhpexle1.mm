include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wtru.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "lhpexle.mm"
include "tru.mm"
include "jctr.mm"
include "reximi.mm"
include "syl.mm"
include "cplt.mm"
include "cfv.mm"
include "cbs.mm"
include "simpll.mm"
include "simprl.mm"
include "eqid.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "lhplt.mm"
include "2atlt.mm"
include "syl31anc.mm"
include "simp3r.mm"
include "wi.mm"
include "simp1ll.mm"
include "simp2.mm"
include "simp1lr.mm"
include "pltle.mm"
include "syl3anc.mm"
include "mpd.mm"
include "a1tru.mm"
include "simp3l.mm"
include "3jca.mm"
include "3expia.mm"
include "reximdva.mm"
include "lhpexle1lem.mm"
include "3simpb.mm"

theorem lhpexle1
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vp: setvar p
  let cY: class Y
  let cZ: class Z
  assume lhpex1.l: |- .<_ = ( le ` K )
  assume lhpex1.a: |- A = ( Atoms ` K )
  assume lhpex1.h: |- H = ( LHyp ` K )

  disjoint .<_ p
  disjoint A p
  disjoint H p
  disjoint K p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A ( p .<_ W /\ p =/= X ) )

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
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    wtru
    @3
    cX
    wne
    #
    w3a
    #
    vp
    cA
    wrex
    #
    @4
    @5
    wa
    #
    vp
    cA
    wrex
    @2
    wtru
    cA
    c.le
    cW
    cX
    vp
    @2
    @4
    vp
    cA
    wrex
    @4
    wtru
    wa
    #
    vp
    cA
    wrex
    cA
    cH
    cK
    c.le
    cW
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle
    @4
    @9
    vp
    cA
    @4
    wtru
    tru
    jctr
    reximi
    syl
    @2
    cX
    cA
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @5
    @3
    cW
    cK
    cplt
    cfv
    #
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @7
    @13
    @0
    @10
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    cX
    cW
    @14
    wbr
    @17
    @0
    @1
    @12
    simpll
    @2
    @10
    @11
    simprl
    @1
    @19
    @0
    @12
    @18
    cH
    cK
    cW
    @18
    eqid
    #
    lhpex1.h
    lhpbase
    ad2antlr
    cA
    cX
    @14
    cH
    cK
    c.le
    cW
    lhpex1.l
    @14
    eqid
    #
    lhpex1.a
    lhpex1.h
    lhplt
    cA
    @18
    cX
    @14
    cK
    cW
    vp
    @20
    @21
    lhpex1.a
    2atlt
    syl31anc
    @13
    @16
    @6
    vp
    cA
    @13
    @3
    cA
    wcel
    #
    @16
    @6
    @13
    @22
    @16
    w3a
    #
    @4
    wtru
    @5
    @23
    @15
    @4
    @13
    @22
    @5
    @15
    simp3r
    @23
    @0
    @22
    @1
    @15
    @4
    wi
    @0
    @1
    @12
    @22
    @16
    simp1ll
    @13
    @22
    @16
    simp2
    @0
    @1
    @12
    @22
    @16
    simp1lr
    chlt
    cA
    cH
    @14
    cK
    c.le
    @3
    cW
    lhpex1.l
    @21
    pltle
    syl3anc
    mpd
    @23
    a1tru
    @13
    @22
    @5
    @15
    simp3l
    3jca
    3expia
    reximdva
    mpd
    lhpexle1lem
    @6
    @8
    vp
    cA
    @4
    wtru
    @5
    3simpb
    reximi
    syl
end
