include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "wo.mm"
include "simplr.mm"
include "simpr.mm"
include "wi.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "simp-4l.mm"
include "simprl.mm"
include "zsubcld.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "ex.mm"
include "znegcld.mm"
include "orim12d.mm"
include "expimpd.mm"
include "3impia.mm"

theorem dvdsacongtr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) /\ ( D || A /\ ( A || ( B - C ) \/ A || ( B - -u C ) ) ) ) -> ( D || ( B - C ) \/ D || ( B - -u C ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cD
    cA
    cdvds
    wbr
    #
    cA
    cB
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    cB
    cC
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    #
    wa
    cD
    @7
    cdvds
    wbr
    #
    cD
    @10
    cdvds
    wbr
    #
    wo
    #
    @2
    @5
    wa
    #
    @6
    @12
    @15
    @16
    @6
    wa
    #
    @8
    @13
    @11
    @14
    @17
    @8
    @13
    @17
    @8
    wa
    #
    @6
    @8
    @13
    @16
    @6
    @8
    simplr
    @17
    @8
    simpr
    @18
    @4
    @0
    @7
    cz
    wcel
    @6
    @8
    wa
    @13
    wi
    @16
    @4
    @6
    @8
    @2
    @3
    @4
    simprr
    #
    ad2antrr
    @0
    @1
    @5
    @6
    @8
    simp-4l
    @18
    cB
    cC
    @16
    @1
    @6
    @8
    @0
    @1
    @5
    simplr
    #
    ad2antrr
    @16
    @3
    @6
    @8
    @2
    @3
    @4
    simprl
    #
    ad2antrr
    zsubcld
    cD
    cA
    @7
    dvdstr
    syl3anc
    mp2and
    ex
    @17
    @11
    @14
    @17
    @11
    wa
    #
    @6
    @11
    @14
    @16
    @6
    @11
    simplr
    @17
    @11
    simpr
    @22
    @4
    @0
    @10
    cz
    wcel
    @6
    @11
    wa
    @14
    wi
    @16
    @4
    @6
    @11
    @19
    ad2antrr
    @0
    @1
    @5
    @6
    @11
    simp-4l
    @22
    cB
    @9
    @16
    @1
    @6
    @11
    @20
    ad2antrr
    @22
    cC
    @16
    @3
    @6
    @11
    @21
    ad2antrr
    znegcld
    zsubcld
    cD
    cA
    @10
    dvdstr
    syl3anc
    mp2and
    ex
    orim12d
    expimpd
    3impia
end
