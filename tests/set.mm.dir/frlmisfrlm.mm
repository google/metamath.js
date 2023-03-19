include "cnzr.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cfrlm.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "clmic.mm"
include "clmod.mm"
include "cuvc.mm"
include "crn.mm"
include "clbs.mm"
include "crg.mm"
include "nzrring.mm"
include "eqid.mm"
include "frlmlmod.mm"
include "sylan.mm"
include "3adant3.mm"
include "frlmlbs.mm"
include "simp3.mm"
include "ensymd.mm"
include "uvcendim.mm"
include "entr.mm"
include "syl2anc.mm"
include "lbslcic.mm"
include "syl3anc.mm"
include "wceq.mm"
include "frlmsca.mm"
include "oveq1d.mm"
include "breqtrrd.mm"

theorem frlmisfrlm
  let cR: class R
  let cI: class I
  let cJ: class J
  let cY: class Y


  assert |- ( ( R e. NzRing /\ I e. Y /\ I ~~ J ) -> ( R freeLMod I ) ~=m ( R freeLMod J ) )

  proof
    cR
    cnzr
    wcel
    #
    cI
    cY
    wcel
    #
    cI
    cJ
    cen
    wbr
    #
    w3a
    #
    cR
    cI
    cfrlm
    co
    #
    @4
    csca
    cfv
    #
    cJ
    cfrlm
    co
    #
    cR
    cJ
    cfrlm
    co
    clmic
    @3
    @4
    clmod
    wcel
    #
    cR
    cI
    cuvc
    co
    #
    crn
    #
    @4
    clbs
    cfv
    #
    wcel
    #
    cJ
    @9
    cen
    wbr
    #
    @4
    @6
    clmic
    wbr
    @0
    @1
    @7
    @2
    @0
    cR
    crg
    wcel
    #
    @1
    @7
    cR
    nzrring
    #
    cR
    @4
    cI
    cY
    @4
    eqid
    #
    frlmlmod
    sylan
    3adant3
    @0
    @1
    @11
    @2
    @0
    @13
    @1
    @11
    @14
    cR
    @8
    @4
    cI
    @10
    cY
    @15
    @8
    eqid
    #
    @10
    eqid
    #
    frlmlbs
    sylan
    3adant3
    @3
    cJ
    cI
    cen
    wbr
    cI
    @9
    cen
    wbr
    #
    @12
    @3
    cI
    cJ
    @0
    @1
    @2
    simp3
    ensymd
    @0
    @1
    @18
    @2
    cR
    @8
    cI
    cY
    @16
    uvcendim
    3adant3
    cJ
    cI
    @9
    entr
    syl2anc
    @9
    @5
    cJ
    @10
    @4
    @5
    eqid
    @17
    lbslcic
    syl3anc
    @3
    cR
    @5
    cJ
    cfrlm
    @0
    @1
    cR
    @5
    wceq
    @2
    cR
    @4
    cI
    cnzr
    cY
    @15
    frlmsca
    3adant3
    oveq1d
    breqtrrd
end
