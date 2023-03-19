include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "cop.mm"
include "elima2.mm"
include "df-br.mm"
include "anbi2i.mm"
include "exbii.mm"
include "bitri.mm"

theorem elima3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume elima.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A e. ( B " C ) <-> E. x ( x e. C /\ <. x , A >. e. B ) )

  proof
    cA
    cB
    cC
    cima
    wcel
    vx
    cv
    #
    cC
    wcel
    #
    @0
    cA
    cB
    wbr
    #
    wa
    #
    vx
    wex
    @1
    @0
    cA
    cop
    cB
    wcel
    #
    wa
    #
    vx
    wex
    vx
    cA
    cB
    cC
    elima.1
    elima2
    @3
    @5
    vx
    @2
    @4
    @1
    @0
    cA
    cB
    df-br
    anbi2i
    exbii
    bitri
end
