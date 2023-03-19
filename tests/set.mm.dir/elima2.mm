include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "elima.mm"
include "df-rex.mm"
include "bitri.mm"

theorem elima2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume elima.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A e. ( B " C ) <-> E. x ( x e. C /\ x B A ) )

  proof
    cA
    cB
    cC
    cima
    wcel
    vx
    cv
    #
    cA
    cB
    wbr
    #
    vx
    cC
    wrex
    @0
    cC
    wcel
    @1
    wa
    vx
    wex
    vx
    cA
    cB
    cC
    elima.1
    elima
    @1
    vx
    cC
    df-rex
    bitri
end
