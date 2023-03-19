include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "ssonunii.mm"
include "unissb.mm"
include "rabbii.mm"
include "inteqi.mm"
include "intmin.mm"
include "syl5reqr.mm"
include "syl.mm"

theorem bm2.5ii
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume bm2.5ii.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A C_ On -> U. A = |^| { x e. On | A. y e. A y C_ x } )

  proof
    cA
    con0
    wss
    cA
    cuni
    #
    con0
    wcel
    #
    @0
    vy
    cv
    vx
    cv
    #
    wss
    vy
    cA
    wral
    #
    vx
    con0
    crab
    #
    cint
    #
    wceq
    cA
    bm2.5ii.1
    ssonunii
    @1
    @5
    @0
    @2
    wss
    #
    vx
    con0
    crab
    #
    cint
    @0
    @7
    @4
    @6
    @3
    vx
    con0
    vy
    cA
    @2
    unissb
    rabbii
    inteqi
    vx
    @0
    con0
    intmin
    syl5reqr
    syl
end
