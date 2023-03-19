include "wf1o.mm"
include "cvv.mm"
include "wcel.mm"
include "wfo.mm"
include "f1ofo.mm"
include "fornex.mm"
include "syl5com.mm"
include "wf1.mm"
include "wi.mm"
include "f1of1.mm"
include "f1dmex.mm"
include "ex.mm"
include "syl.mm"
include "impbid.mm"

theorem f1ovv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> ( A e. _V <-> B e. _V ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @0
    cA
    cB
    cF
    wfo
    @1
    @2
    cA
    cB
    cF
    f1ofo
    cA
    cB
    cvv
    cF
    fornex
    syl5com
    @0
    cA
    cB
    cF
    wf1
    #
    @2
    @1
    wi
    cA
    cB
    cF
    f1of1
    @3
    @2
    @1
    cA
    cB
    cvv
    cF
    f1dmex
    ex
    syl
    impbid
end
