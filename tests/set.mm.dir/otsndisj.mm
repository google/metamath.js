include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "cv.mm"
include "cotp.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "wb.mm"
include "otthg.mm"
include "3expa.mm"
include "simp3.mm"
include "syl6bi.mm"
include "con3rr3.mm"
include "imp.mm"
include "neqned.mm"
include "disjsn2.mm"
include "syl.mm"
include "expcom.mm"
include "orrd.mm"
include "adantrr.mm"
include "ralrimivva.mm"
include "oteq3.mm"
include "sneqd.mm"
include "disjor.mm"
include "sylibr.mm"

theorem otsndisj
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d

  disjoint A c
  disjoint B c
  disjoint V c
  disjoint X c
  disjoint Y c
  disjoint A d
  disjoint c d
  disjoint B d
  disjoint V d
  disjoint X d
  disjoint Y d
  assert |- ( ( A e. X /\ B e. Y ) -> Disj_ c e. V { <. A , B , c >. } )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    vc
    vd
    weq
    #
    cA
    cB
    vc
    cv
    #
    cotp
    #
    csn
    #
    cA
    cB
    vd
    cv
    #
    cotp
    #
    csn
    #
    cin
    c0
    wceq
    #
    wo
    #
    vd
    cV
    wral
    vc
    cV
    wral
    vc
    cV
    @6
    wdisj
    @2
    @11
    vc
    vd
    cV
    cV
    @2
    @4
    cV
    wcel
    #
    @11
    @7
    cV
    wcel
    @2
    @12
    wa
    #
    @3
    @10
    @3
    wn
    #
    @13
    @10
    @14
    @13
    wa
    #
    @5
    @8
    wne
    @10
    @15
    @5
    @8
    @14
    @13
    @5
    @8
    wceq
    #
    wn
    @13
    @16
    @3
    @13
    @16
    cA
    cA
    wceq
    #
    cB
    cB
    wceq
    #
    @3
    w3a
    #
    @3
    @0
    @1
    @12
    @16
    @19
    wb
    cA
    cB
    @4
    cA
    cX
    cB
    @7
    cY
    cV
    otthg
    3expa
    @17
    @18
    @3
    simp3
    syl6bi
    con3rr3
    imp
    neqned
    @5
    @8
    disjsn2
    syl
    expcom
    orrd
    adantrr
    ralrimivva
    cV
    @6
    @9
    vc
    vd
    @3
    @5
    @8
    @4
    @7
    cA
    cB
    oteq3
    sneqd
    disjor
    sylibr
end
