include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "elfzoel1.mm"
include "adantr.mm"
include "zred.mm"
include "elfzoelz.mm"
include "simpr.mm"
include "elfzole1.mm"
include "leadd1dd.mm"
include "elfzoel2.mm"
include "elfzolt2.mm"
include "ltadd1dd.mm"
include "wb.mm"
include "zaddcl.mm"
include "sylan.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem fzoaddel
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( B ..^ C ) /\ D e. ZZ ) -> ( A + D ) e. ( ( B + D ) ..^ ( C + D ) ) )

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
    caddc
    co
    #
    cB
    cD
    caddc
    co
    #
    cC
    cD
    caddc
    co
    #
    cfzo
    co
    wcel
    #
    @4
    @3
    cle
    wbr
    #
    @3
    @5
    clt
    wbr
    #
    @2
    cB
    cA
    cD
    @2
    cB
    @0
    cB
    cz
    wcel
    #
    @1
    cA
    cB
    cC
    elfzoel1
    #
    adantr
    zred
    @2
    cA
    @0
    cA
    cz
    wcel
    #
    @1
    cA
    cB
    cC
    elfzoelz
    #
    adantr
    zred
    #
    @2
    cD
    @0
    @1
    simpr
    zred
    #
    @0
    cB
    cA
    cle
    wbr
    @1
    cA
    cB
    cC
    elfzole1
    adantr
    leadd1dd
    @2
    cA
    cC
    cD
    @13
    @2
    cC
    @0
    cC
    cz
    wcel
    #
    @1
    cA
    cB
    cC
    elfzoel2
    #
    adantr
    zred
    @14
    @0
    cA
    cC
    clt
    wbr
    @1
    cA
    cB
    cC
    elfzolt2
    adantr
    ltadd1dd
    @2
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @6
    @7
    @8
    wa
    wb
    @0
    @11
    @1
    @17
    @12
    cA
    cD
    zaddcl
    sylan
    @0
    @9
    @1
    @18
    @10
    cB
    cD
    zaddcl
    sylan
    @0
    @15
    @1
    @19
    @16
    cC
    cD
    zaddcl
    sylan
    @3
    @4
    @5
    elfzo
    syl3anc
    mpbir2and
end
