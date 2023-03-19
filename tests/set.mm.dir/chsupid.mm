include "cch.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "chsup.mm"
include "cfv.mm"
include "cuni.mm"
include "cint.mm"
include "wceq.mm"
include "ssrab2.mm"
include "chsupval2.mm"
include "ax-mp.mm"
include "unimax.mm"
include "sseq1d.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "intmin.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem chsupid
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A e. CH -> ( \/H ` { x e. CH | x C_ A } ) = A )

  proof
    cA
    cch
    wcel
    #
    vx
    cv
    cA
    wss
    #
    vx
    cch
    crab
    #
    chsup
    cfv
    #
    @2
    cuni
    #
    vy
    cv
    #
    wss
    #
    vy
    cch
    crab
    #
    cint
    #
    cA
    @2
    cch
    wss
    @3
    @8
    wceq
    @1
    vx
    cch
    ssrab2
    vy
    @2
    chsupval2
    ax-mp
    @0
    @8
    cA
    @5
    wss
    #
    vy
    cch
    crab
    #
    cint
    cA
    @0
    @7
    @10
    @0
    @6
    @9
    vy
    cch
    @0
    @4
    cA
    @5
    vx
    cA
    cch
    unimax
    sseq1d
    rabbidv
    inteqd
    vy
    cA
    cch
    intmin
    eqtrd
    syl5eq
end
