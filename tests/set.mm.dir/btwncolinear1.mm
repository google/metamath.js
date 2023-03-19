include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccolin.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "w3o.mm"
include "3mix3.mm"
include "brcolinear.mm"
include "syl5ibr.mm"

theorem btwncolinear1
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( C Btwn <. A , B >. -> A Colinear <. B , C >. ) )

  proof
    cC
    cA
    cB
    cop
    cbtwn
    wbr
    #
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @2
    wcel
    cC
    @2
    wcel
    w3a
    wa
    cA
    @1
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    #
    @0
    w3o
    @0
    @3
    @4
    3mix3
    cA
    cB
    cC
    cN
    brcolinear
    syl5ibr
end
