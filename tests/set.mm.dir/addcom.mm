include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cmul.mm"
include "1cnd.mm"
include "addcld.mm"
include "simpl.mm"
include "simpr.mm"
include "adddid.mm"
include "1p1times.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr3rd.mm"
include "addassd.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "addcan2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "3eqtr3d.mm"
include "addcan.mm"

theorem addcom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + B ) = ( B + A ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cA
    cB
    caddc
    co
    #
    caddc
    co
    #
    cA
    cB
    cA
    caddc
    co
    #
    caddc
    co
    #
    wceq
    #
    @3
    @5
    wceq
    #
    @2
    cA
    cA
    caddc
    co
    #
    cB
    caddc
    co
    #
    @3
    cA
    caddc
    co
    #
    @4
    @6
    @2
    @10
    cB
    caddc
    co
    #
    @11
    cB
    caddc
    co
    #
    wceq
    #
    @10
    @11
    wceq
    #
    @2
    @9
    cB
    cB
    caddc
    co
    #
    caddc
    co
    #
    @3
    @3
    caddc
    co
    #
    @12
    @13
    @2
    c1
    c1
    caddc
    co
    #
    @3
    cmul
    co
    #
    @19
    cA
    cmul
    co
    #
    @19
    cB
    cmul
    co
    #
    caddc
    co
    @18
    @17
    @2
    @19
    cA
    cB
    @2
    c1
    c1
    @2
    1cnd
    #
    @23
    addcld
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    adddid
    @2
    @3
    cc
    wcel
    #
    @20
    @18
    wceq
    @2
    cA
    cB
    @24
    @25
    addcld
    #
    @3
    1p1times
    syl
    @0
    @1
    @21
    @9
    @22
    @16
    caddc
    cA
    1p1times
    cB
    1p1times
    oveqan12d
    3eqtr3rd
    @2
    @9
    cB
    cB
    @2
    cA
    cA
    @24
    @24
    addcld
    #
    @25
    @25
    addassd
    @2
    @3
    cA
    cB
    @27
    @24
    @25
    addassd
    3eqtr4d
    @2
    @10
    cc
    wcel
    @11
    cc
    wcel
    @1
    @14
    @15
    wb
    @2
    @9
    cB
    @28
    @25
    addcld
    @2
    @3
    cA
    @27
    @24
    addcld
    @25
    @10
    @11
    cB
    addcan2
    syl3anc
    mpbid
    @2
    cA
    cA
    cB
    @24
    @24
    @25
    addassd
    @2
    cA
    cB
    cA
    @24
    @25
    @24
    addassd
    3eqtr3d
    @2
    @0
    @26
    @5
    cc
    wcel
    @7
    @8
    wb
    @24
    @27
    @2
    cB
    cA
    @25
    @24
    addcld
    cA
    @3
    @5
    addcan
    syl3anc
    mpbid
end
