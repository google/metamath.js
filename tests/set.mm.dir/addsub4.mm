include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "addsub.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "addcld.mm"
include "simprr.mm"
include "subsub4.mm"
include "subcl.mm"
include "ad2ant2r.mm"
include "addsubass.mm"
include "3eqtr3d.mm"

theorem addsub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A + B ) - ( C + D ) ) = ( ( A - C ) + ( B - D ) ) )

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
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cC
    cmin
    co
    #
    cD
    cmin
    co
    #
    cA
    cC
    cmin
    co
    #
    cB
    caddc
    co
    #
    cD
    cmin
    co
    #
    @7
    cC
    cD
    caddc
    co
    cmin
    co
    #
    @10
    cB
    cD
    cmin
    co
    caddc
    co
    #
    @6
    @8
    @11
    cD
    cmin
    @6
    @0
    @1
    @3
    @8
    @11
    wceq
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    #
    @2
    @3
    @4
    simprl
    #
    cA
    cB
    cC
    addsub
    syl3anc
    oveq1d
    @6
    @7
    cc
    wcel
    @3
    @4
    @9
    @13
    wceq
    @6
    cA
    cB
    @15
    @16
    addcld
    @17
    @2
    @3
    @4
    simprr
    #
    @7
    cC
    cD
    subsub4
    syl3anc
    @6
    @10
    cc
    wcel
    #
    @1
    @4
    @12
    @14
    wceq
    @0
    @3
    @19
    @1
    @4
    cA
    cC
    subcl
    ad2ant2r
    @16
    @18
    @10
    cB
    cD
    addsubass
    syl3anc
    3eqtr3d
end
