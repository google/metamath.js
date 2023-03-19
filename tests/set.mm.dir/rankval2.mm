include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "csuc.mm"
include "cr1.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "rankvalg.mm"
include "cpw.mm"
include "r1suc.mm"
include "eleq2d.mm"
include "fvex.mm"
include "elpw2.mm"
include "syl6bb.mm"
include "rabbiia.mm"
include "inteqi.mm"
include "syl6eq.mm"

theorem rankval2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. B -> ( rank ` A ) = |^| { x e. On | A C_ ( R1 ` x ) } )

  proof
    cA
    cB
    wcel
    cA
    crnk
    cfv
    cA
    vx
    cv
    #
    csuc
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    cA
    @0
    cr1
    cfv
    #
    wss
    #
    vx
    con0
    crab
    #
    cint
    vx
    cA
    cB
    rankvalg
    @3
    @6
    @2
    @5
    vx
    con0
    @0
    con0
    wcel
    #
    @2
    cA
    @4
    cpw
    #
    wcel
    @5
    @7
    @1
    @8
    cA
    @0
    r1suc
    eleq2d
    cA
    @4
    @0
    cr1
    fvex
    elpw2
    syl6bb
    rabbiia
    inteqi
    syl6eq
end
