include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cgrcomim.mm"
include "wi.mm"
include "3com23.mm"
include "impbid.mm"

theorem cgrcom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( <. A , B >. Cgr <. C , D >. <-> <. C , D >. Cgr <. A , B >. ) )

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
    cB
    @1
    wcel
    wa
    #
    cC
    @1
    wcel
    cD
    @1
    wcel
    wa
    #
    w3a
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
    @5
    @4
    ccgr
    wbr
    #
    cA
    cB
    cC
    cD
    cN
    cgrcomim
    @0
    @3
    @2
    @7
    @6
    wi
    cC
    cD
    cA
    cB
    cN
    cgrcomim
    3com23
    impbid
end
