include "cch.mm"
include "wss.mm"
include "chil.mm"
include "cpw.mm"
include "chsup.mm"
include "cfv.mm"
include "cuni.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "chsspwh.mm"
include "sstr2.mm"
include "mpi.mm"
include "hsupval2.mm"
include "syl.mm"

theorem chsupval2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A C_ CH -> ( \/H ` A ) = |^| { x e. CH | U. A C_ x } )

  proof
    cA
    cch
    wss
    #
    cA
    chil
    cpw
    #
    wss
    #
    cA
    chsup
    cfv
    cA
    cuni
    vx
    cv
    wss
    vx
    cch
    crab
    cint
    wceq
    @0
    cch
    @1
    wss
    @2
    chsspwh
    cA
    cch
    @1
    sstr2
    mpi
    vx
    cA
    hsupval2
    syl
end
