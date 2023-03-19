include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "dfima2.mm"
include "df-br.mm"
include "rexbii.mm"
include "df-rex.mm"
include "bitri.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfima3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( A " B ) = { y | E. x ( x e. B /\ <. x , y >. e. A ) }

  proof
    cA
    cB
    cima
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vx
    cB
    wrex
    #
    vy
    cab
    @0
    cB
    wcel
    @0
    @1
    cop
    cA
    wcel
    #
    wa
    vx
    wex
    #
    vy
    cab
    vx
    vy
    cA
    cB
    dfima2
    @3
    @5
    vy
    @3
    @4
    vx
    cB
    wrex
    @5
    @2
    @4
    vx
    cB
    @0
    @1
    cA
    df-br
    rexbii
    @4
    vx
    cB
    df-rex
    bitri
    abbii
    eqtri
end
