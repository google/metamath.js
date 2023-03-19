include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "simprr.mm"
include "lhpexle1.mm"
include "adantr.mm"
include "jca.mm"
include "necom.mm"
include "3anbi3i.mm"
include "3anass.mm"
include "bitri.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "bitr2i.mm"
include "sylib.mm"
include "lhpexle.mm"
include "reximddv.mm"

theorem lhpex2leN
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  assume lhp2at.l: |- .<_ = ( le ` K )
  assume lhp2at.a: |- A = ( Atoms ` K )
  assume lhp2at.h: |- H = ( LHyp ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint W p
  disjoint W q
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A E. q e. A ( p .<_ W /\ q .<_ W /\ p =/= q ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    @2
    vq
    cv
    #
    cW
    c.le
    wbr
    #
    @1
    @3
    wne
    #
    w3a
    #
    vq
    cA
    wrex
    #
    vp
    cA
    @0
    @1
    cA
    wcel
    #
    @2
    wa
    #
    wa
    #
    @2
    @4
    @3
    @1
    wne
    #
    wa
    #
    vq
    cA
    wrex
    #
    wa
    #
    @7
    @10
    @2
    @13
    @0
    @8
    @2
    simprr
    @0
    @13
    @9
    cA
    cH
    cK
    c.le
    cW
    @1
    vq
    lhp2at.l
    lhp2at.a
    lhp2at.h
    lhpexle1
    adantr
    jca
    @7
    @2
    @12
    wa
    #
    vq
    cA
    wrex
    @14
    @6
    @15
    vq
    cA
    @6
    @2
    @4
    @11
    w3a
    @15
    @5
    @11
    @2
    @4
    @1
    @3
    necom
    3anbi3i
    @2
    @4
    @11
    3anass
    bitri
    rexbii
    @2
    @12
    vq
    cA
    r19.42v
    bitr2i
    sylib
    cA
    cH
    cK
    c.le
    cW
    vp
    lhp2at.l
    lhp2at.a
    lhp2at.h
    lhpexle
    reximddv
end
