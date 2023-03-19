include "wcel.mm"
include "ccnv.mm"
include "cvv.mm"
include "ccoss.mm"
include "cnvexg.mm"
include "cossex.mm"
include "syl.mm"

theorem cosscnvex
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ,~ `' A e. _V )

  proof
    cA
    cV
    wcel
    cA
    ccnv
    #
    cvv
    wcel
    @0
    ccoss
    cvv
    wcel
    cA
    cV
    cnvexg
    @0
    cvv
    cossex
    syl
end
