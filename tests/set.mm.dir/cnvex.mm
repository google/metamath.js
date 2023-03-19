include "cvv.mm"
include "wcel.mm"
include "ccnv.mm"
include "cnvexg.mm"
include "ax-mp.mm"

theorem cnvex
  let cA: class A
  assume cnvex.1: |- A e. _V


  assert |- `' A e. _V

  proof
    cA
    cvv
    wcel
    cA
    ccnv
    cvv
    wcel
    cnvex.1
    cA
    cvv
    cnvexg
    ax-mp
end
