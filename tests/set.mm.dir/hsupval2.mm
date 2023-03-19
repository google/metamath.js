include "chil.mm"
include "cpw.mm"
include "wss.mm"
include "chsup.mm"
include "cfv.mm"
include "cuni.mm"
include "cort.mm"
include "cv.mm"
include "cch.mm"
include "crab.mm"
include "cint.mm"
include "hsupval.mm"
include "wceq.mm"
include "sspwuni.mm"
include "ococin.mm"
include "sylbi.mm"
include "eqtrd.mm"

theorem hsupval2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A C_ ~P ~H -> ( \/H ` A ) = |^| { x e. CH | U. A C_ x } )

  proof
    cA
    chil
    cpw
    wss
    #
    cA
    chsup
    cfv
    cA
    cuni
    #
    cort
    cfv
    cort
    cfv
    #
    @1
    vx
    cv
    wss
    vx
    cch
    crab
    cint
    #
    cA
    hsupval
    @0
    @1
    chil
    wss
    @2
    @3
    wceq
    cA
    chil
    sspwuni
    vx
    @1
    ococin
    sylbi
    eqtrd
end
