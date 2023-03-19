include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cc.mm"
include "simpr.mm"
include "recnd.mm"
include "adantr.mm"
include "simpl.mm"
include "adantl.mm"
include "addsubd.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "simprr.mm"
include "simprl.mm"
include "resubcl.mm"
include "ancoms.mm"
include "ltsubaddd.mm"
include "readdcl.mm"
include "ad2ant2lr.mm"
include "ltaddsub2d.mm"
include "3bitr4d.mm"

theorem ltsubadd2b
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( D - C ) < ( B - A ) <-> ( A + D ) < ( B + C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    wa
    #
    cD
    cB
    cA
    cmin
    co
    #
    cC
    caddc
    co
    #
    clt
    wbr
    cD
    cB
    cC
    caddc
    co
    #
    cA
    cmin
    co
    #
    clt
    wbr
    cD
    cC
    cmin
    co
    @7
    clt
    wbr
    cA
    cD
    caddc
    co
    @9
    clt
    wbr
    @6
    @8
    @10
    cD
    clt
    @6
    @10
    @8
    @6
    cB
    cC
    cA
    @2
    cB
    cc
    wcel
    @5
    @2
    cB
    @0
    @1
    simpr
    recnd
    adantr
    @5
    cC
    cc
    wcel
    @2
    @5
    cC
    @3
    @4
    simpl
    recnd
    adantl
    @2
    cA
    cc
    wcel
    @5
    @2
    cA
    @0
    @1
    simpl
    #
    recnd
    adantr
    addsubd
    eqcomd
    breq2d
    @6
    cD
    cC
    @7
    @2
    @3
    @4
    simprr
    #
    @2
    @3
    @4
    simprl
    @2
    @7
    cr
    wcel
    #
    @5
    @1
    @0
    @13
    cB
    cA
    resubcl
    ancoms
    adantr
    ltsubaddd
    @6
    cA
    cD
    @9
    @2
    @0
    @5
    @11
    adantr
    @12
    @1
    @3
    @9
    cr
    wcel
    @0
    @4
    cB
    cC
    readdcl
    ad2ant2lr
    ltaddsub2d
    3bitr4d
end
