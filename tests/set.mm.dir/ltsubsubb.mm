include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cc.mm"
include "wceq.mm"
include "simprl.mm"
include "recnd.mm"
include "simprr.mm"
include "simplr.mm"
include "w3a.mm"
include "subadd23.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "simpll.mm"
include "resubcl.mm"
include "ad2ant2l.mm"
include "ltsubadd2d.mm"
include "adantl.mm"
include "ltsubaddd.mm"
include "3bitr4d.mm"

theorem ltsubsubb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( A - C ) < ( B - D ) <-> ( A - B ) < ( C - D ) ) )

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
    cC
    cB
    cD
    cmin
    co
    #
    caddc
    co
    #
    clt
    wbr
    cA
    cC
    cD
    cmin
    co
    #
    cB
    caddc
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
    cB
    cmin
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
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @8
    @10
    wceq
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
    recnd
    @6
    cB
    @0
    @1
    @5
    simplr
    #
    recnd
    @11
    @12
    @13
    w3a
    @10
    @8
    cC
    cD
    cB
    subadd23
    eqcomd
    syl3anc
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
    @14
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
    ltsubadd2d
    @6
    cA
    cB
    @9
    @16
    @15
    @5
    @9
    cr
    wcel
    @2
    cC
    cD
    resubcl
    adantl
    ltsubaddd
    3bitr4d
end
