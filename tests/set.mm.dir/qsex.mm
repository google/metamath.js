include "cvv.mm"
include "wcel.mm"
include "cqs.mm"
include "qsexg.mm"
include "ax-mp.mm"

theorem qsex
  let cA: class A
  let cR: class R
  assume qsex.1: |- A e. _V


  assert |- ( A /. R ) e. _V

  proof
    cA
    cvv
    wcel
    cA
    cR
    cqs
    cvv
    wcel
    qsex.1
    cA
    cR
    cvv
    qsexg
    ax-mp
end
