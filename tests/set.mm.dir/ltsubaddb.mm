include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "simplr.mm"
include "recnd.mm"
include "simprl.mm"
include "simprr.mm"
include "addsubd.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "simpll.mm"
include "resubcl.mm"
include "ad2ant2l.mm"
include "ltsubaddd.mm"
include "readdcl.mm"
include "ad2ant2lr.mm"
include "ltaddsubd.mm"
include "3bitr4d.mm"

theorem ltsubaddb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A - C ) < ( B - D ) <-> ( A + D ) < ( B + C ) ) )

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
    cA
    cB
    cD
    cmin
    co
    #
    cC
    caddc
    co
    #
    clt
    wbr
    cA
    cB
    cC
    caddc
    co
    #
    cD
    cmin
    co
    #
    clt
    wbr
    cA
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
    cA
    clt
    @6
    @10
    @8
    @6
    cB
    cC
    cD
    @6
    cB
    @0
    @1
    @5
    simplr
    recnd
    @6
    cC
    @2
    @3
    @4
    simprl
    #
    recnd
    @6
    cD
    @2
    @3
    @4
    simprr
    #
    recnd
    addsubd
    eqcomd
    breq2d
    @6
    cA
    cC
    @7
    @0
    @1
    @5
    simpll
    #
    @11
    @1
    @4
    @7
    cr
    wcel
    @0
    @3
    cB
    cD
    resubcl
    ad2ant2l
    ltsubaddd
    @6
    cA
    cD
    @9
    @13
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
    ltaddsubd
    3bitr4d
end
