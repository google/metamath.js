include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "colinearperm4.mm"
include "wb.mm"
include "3anrot.mm"
include "colinearperm1.mm"
include "sylan2br.mm"
include "bitrd.mm"

theorem colinearperm5
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Colinear <. B , C >. <-> C Colinear <. B , A >. ) )

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
    cC
    cA
    cB
    cop
    ccolin
    wbr
    #
    cC
    cB
    cA
    cop
    ccolin
    wbr
    #
    cA
    cB
    cC
    cN
    colinearperm4
    @5
    @0
    @4
    @2
    @3
    w3a
    @6
    @7
    wb
    @4
    @2
    @3
    3anrot
    cC
    cA
    cB
    cN
    colinearperm1
    sylan2br
    bitrd
end
