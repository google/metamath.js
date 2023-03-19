include "cint.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "ciin.mm"
include "intimass.mm"
include "intima0.mm"
include "sseqtr4i.mm"

theorem intimass2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( |^| A " B ) C_ |^|_ x e. A ( x " B )

  proof
    cA
    cint
    cB
    cima
    vy
    cv
    vx
    cv
    cB
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
    @0
    ciin
    vy
    cA
    cB
    vx
    intimass
    vy
    cA
    cB
    vx
    intima0
    sseqtr4i
end
