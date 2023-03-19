include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wa.mm"
include "simp1.mm"
include "simp23.mm"
include "simp31.mm"
include "simp21.mm"
include "simp22.mm"
include "simp32.mm"
include "simp33.mm"
include "simprl.mm"
include "cgrcomand.mm"
include "simprr.mm"
include "cgrtr4and.mm"
include "ex.mm"

theorem cgrtr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( <. A , B >. Cgr <. C , D >. /\ <. C , D >. Cgr <. E , F >. ) -> <. A , B >. Cgr <. E , F >. ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    @12
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    @11
    @14
    ccgr
    wbr
    @10
    @16
    cC
    cD
    cA
    cB
    cE
    cF
    cN
    @0
    @5
    @9
    simp1
    #
    @0
    @2
    @3
    @4
    @9
    simp23
    #
    @0
    @5
    @6
    @7
    @8
    simp31
    #
    @0
    @2
    @3
    @4
    @9
    simp21
    #
    @0
    @2
    @3
    @4
    @9
    simp22
    #
    @0
    @5
    @6
    @7
    @8
    simp32
    @0
    @5
    @6
    @7
    @8
    simp33
    @10
    @16
    cA
    cB
    cC
    cD
    cN
    @17
    @20
    @21
    @18
    @19
    @10
    @13
    @15
    simprl
    cgrcomand
    @10
    @13
    @15
    simprr
    cgrtr4and
    ex
end
