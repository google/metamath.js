include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "divdir.mm"
include "syl3an2.mm"
include "negsub.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "eqtr3d.mm"
include "divneg.mm"
include "3expb.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "divcl.mm"
include "3adant2.mm"
include "negsubd.mm"

theorem divsubdir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A - B ) / C ) = ( ( A / C ) - ( B / C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cneg
    #
    cC
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cC
    cdiv
    co
    #
    @6
    cB
    cC
    cdiv
    co
    #
    cmin
    co
    #
    @5
    cA
    @7
    caddc
    co
    #
    cC
    cdiv
    co
    #
    @9
    @11
    @1
    @0
    @7
    cc
    wcel
    @4
    @15
    @9
    wceq
    cB
    negcl
    cA
    @7
    cC
    divdir
    syl3an2
    @0
    @1
    @15
    @11
    wceq
    @4
    @0
    @1
    wa
    @14
    @10
    cC
    cdiv
    cA
    cB
    negsub
    oveq1d
    3adant3
    eqtr3d
    @5
    @6
    @12
    cneg
    #
    caddc
    co
    @9
    @13
    @5
    @16
    @8
    @6
    caddc
    @1
    @4
    @16
    @8
    wceq
    #
    @0
    @1
    @2
    @3
    @17
    cB
    cC
    divneg
    3expb
    3adant1
    oveq2d
    @5
    @6
    @12
    @0
    @4
    @6
    cc
    wcel
    #
    @1
    @0
    @2
    @3
    @18
    cA
    cC
    divcl
    3expb
    3adant2
    @1
    @4
    @12
    cc
    wcel
    #
    @0
    @1
    @2
    @3
    @19
    cB
    cC
    divcl
    3expb
    3adant1
    negsubd
    eqtr3d
    eqtr3d
end
