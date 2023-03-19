include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "colinearperm3.mm"
include "wb.mm"
include "3anrot.mm"
include "sylan2b.mm"
include "bitrd.mm"

theorem colinearperm4
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Colinear <. B , C >. <-> C Colinear <. A , B >. ) )

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
    wa
    cA
    cB
    cC
    cop
    ccolin
    wbr
    cB
    cC
    cA
    cop
    ccolin
    wbr
    #
    cC
    cA
    cB
    cop
    ccolin
    wbr
    #
    cA
    cB
    cC
    cN
    colinearperm3
    @5
    @0
    @3
    @4
    @2
    w3a
    @6
    @7
    wb
    @2
    @3
    @4
    3anrot
    cB
    cC
    cA
    cN
    colinearperm3
    sylan2b
    bitrd
end
