include "wcel.mm"
include "cint.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "ciin.mm"
include "intimasn.mm"
include "intima0.mm"
include "syl6eqr.mm"

theorem intimasn2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( B e. V -> ( |^| A " { B } ) = |^|_ x e. A ( x " { B } ) )

  proof
    cB
    cV
    wcel
    cA
    cint
    cB
    csn
    #
    cima
    vy
    cv
    vx
    cv
    @0
    cima
    #
    wceq
    vx
    cA
    wrex
    vy
    cab
    cint
    vx
    cA
    @1
    ciin
    vy
    cA
    cB
    cV
    vx
    intimasn
    vy
    cA
    @0
    vx
    intima0
    syl6eqr
end
