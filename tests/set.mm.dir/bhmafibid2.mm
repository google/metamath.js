include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cmul.mm"
include "cmin.mm"
include "simprl.mm"
include "recnd.mm"
include "sqcld.mm"
include "simprr.mm"
include "addcomd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "bhmafibid1.mm"
include "ancom2s.mm"
include "simpll.mm"
include "mulcld.mm"
include "simplr.mm"
include "subcld.mm"
include "addcld.mm"
include "3eqtrd.mm"

theorem bhmafibid2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) ) -> ( ( ( A ^ 2 ) + ( B ^ 2 ) ) x. ( ( C ^ 2 ) + ( D ^ 2 ) ) ) = ( ( ( ( A x. C ) + ( B x. D ) ) ^ 2 ) + ( ( ( A x. D ) - ( B x. C ) ) ^ 2 ) ) )

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
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    cD
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    @7
    @9
    @8
    caddc
    co
    #
    cmul
    co
    #
    cA
    cD
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    cA
    cC
    cmul
    co
    #
    cB
    cD
    cmul
    co
    #
    caddc
    co
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @20
    @16
    caddc
    co
    @6
    @10
    @11
    @7
    cmul
    @6
    @8
    @9
    @6
    cC
    @6
    cC
    @2
    @3
    @4
    simprl
    recnd
    #
    sqcld
    @6
    cD
    @6
    cD
    @2
    @3
    @4
    simprr
    recnd
    #
    sqcld
    addcomd
    oveq2d
    @2
    @4
    @3
    @12
    @21
    wceq
    cA
    cB
    cD
    cC
    bhmafibid1
    ancom2s
    @6
    @16
    @20
    @6
    @15
    @6
    @13
    @14
    @6
    cA
    cD
    @6
    cA
    @0
    @1
    @5
    simpll
    recnd
    #
    @23
    mulcld
    @6
    cB
    cC
    @6
    cB
    @0
    @1
    @5
    simplr
    recnd
    #
    @22
    mulcld
    subcld
    sqcld
    @6
    @19
    @6
    @17
    @18
    @6
    cA
    cC
    @24
    @22
    mulcld
    @6
    cB
    cD
    @25
    @23
    mulcld
    addcld
    sqcld
    addcomd
    3eqtrd
end
