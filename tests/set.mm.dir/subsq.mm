include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "simpl.mm"
include "simpr.mm"
include "subcl.mm"
include "adddird.mm"
include "wceq.mm"
include "subdi.mm"
include "3anidm12.mm"
include "sqval.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "subdid.mm"
include "mulcom.mm"
include "adantl.mm"
include "oveq12d.mm"
include "sqcl.mm"
include "mulcl.mm"
include "npncand.mm"
include "3eqtrrd.mm"

theorem subsq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A ^ 2 ) - ( B ^ 2 ) ) = ( ( A + B ) x. ( A - B ) ) )

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
    cB
    caddc
    co
    cA
    cB
    cmin
    co
    #
    cmul
    co
    cA
    @3
    cmul
    co
    #
    cB
    @3
    cmul
    co
    #
    caddc
    co
    cA
    c2
    cexp
    co
    #
    cA
    cB
    cmul
    co
    #
    cmin
    co
    #
    @7
    cB
    c2
    cexp
    co
    #
    cmin
    co
    #
    caddc
    co
    @6
    @9
    cmin
    co
    @2
    cA
    cB
    @3
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    cA
    cB
    subcl
    adddird
    @2
    @4
    @8
    @5
    @10
    caddc
    @2
    @4
    cA
    cA
    cmul
    co
    #
    @7
    cmin
    co
    #
    @8
    @0
    @1
    @4
    @14
    wceq
    cA
    cA
    cB
    subdi
    3anidm12
    @2
    @6
    @13
    @7
    cmin
    @0
    @6
    @13
    wceq
    @1
    cA
    sqval
    adantr
    oveq1d
    eqtr4d
    @2
    @5
    cB
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    cmin
    co
    @10
    @2
    cB
    cA
    cB
    @12
    @11
    @12
    subdid
    @2
    @7
    @15
    @9
    @16
    cmin
    cA
    cB
    mulcom
    @1
    @9
    @16
    wceq
    @0
    cB
    sqval
    adantl
    oveq12d
    eqtr4d
    oveq12d
    @2
    @6
    @7
    @9
    @0
    @6
    cc
    wcel
    @1
    cA
    sqcl
    adantr
    cA
    cB
    mulcl
    @1
    @9
    cc
    wcel
    @0
    cB
    sqcl
    adantl
    npncand
    3eqtrrd
end
