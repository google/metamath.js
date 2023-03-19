include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "znegcl.mm"
include "fzoaddel.mm"
include "sylan2.mm"
include "elfzoelz.mm"
include "adantr.mm"
include "zcnd.mm"
include "simpr.mm"
include "negsubd.mm"
include "elfzoel1.mm"
include "elfzoel2.mm"
include "oveq12d.mm"
include "3eltr3d.mm"

theorem fzosubel
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( B ..^ C ) /\ D e. ZZ ) -> ( A - D ) e. ( ( B - D ) ..^ ( C - D ) ) )

  proof
    cA
    cB
    cC
    cfzo
    co
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cA
    cD
    cneg
    #
    caddc
    co
    #
    cB
    @3
    caddc
    co
    #
    cC
    @3
    caddc
    co
    #
    cfzo
    co
    #
    cA
    cD
    cmin
    co
    cB
    cD
    cmin
    co
    #
    cC
    cD
    cmin
    co
    #
    cfzo
    co
    @1
    @0
    @3
    cz
    wcel
    @4
    @7
    wcel
    cD
    znegcl
    cA
    cB
    cC
    @3
    fzoaddel
    sylan2
    @2
    cA
    cD
    @2
    cA
    @0
    cA
    cz
    wcel
    @1
    cA
    cB
    cC
    elfzoelz
    adantr
    zcnd
    @2
    cD
    @0
    @1
    simpr
    zcnd
    #
    negsubd
    @2
    @5
    @8
    @6
    @9
    cfzo
    @2
    cB
    cD
    @2
    cB
    @0
    cB
    cz
    wcel
    @1
    cA
    cB
    cC
    elfzoel1
    adantr
    zcnd
    @10
    negsubd
    @2
    cC
    cD
    @2
    cC
    @0
    cC
    cz
    wcel
    @1
    cA
    cB
    cC
    elfzoel2
    adantr
    zcnd
    @10
    negsubd
    oveq12d
    3eltr3d
end
