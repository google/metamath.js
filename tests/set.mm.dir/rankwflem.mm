include "wcel.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wrex.mm"
include "cvv.mm"
include "elex.mm"
include "unir1.mm"
include "syl6eleqr.mm"
include "rankwflemb.mm"
include "sylib.mm"

theorem rankwflem
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> E. x e. On A e. ( R1 ` suc x ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    vx
    cv
    csuc
    cr1
    cfv
    wcel
    vx
    con0
    wrex
    @0
    cA
    cvv
    @1
    cA
    cV
    elex
    unir1
    syl6eleqr
    vx
    cA
    rankwflemb
    sylib
end
