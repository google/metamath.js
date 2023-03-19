include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "cvv.mm"
include "unipr.mm"
include "prex.mm"
include "uniex.mm"
include "eqeltrri.mm"

theorem unex
  let cA: class A
  let cB: class B
  assume unex.1: |- A e. _V
  assume unex.2: |- B e. _V


  assert |- ( A u. B ) e. _V

  proof
    cA
    cB
    cpr
    #
    cuni
    cA
    cB
    cun
    cvv
    cA
    cB
    unex.1
    unex.2
    unipr
    @0
    cA
    cB
    prex
    uniex
    eqeltrri
end
