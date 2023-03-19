include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "cuni.mm"
include "csuc.mm"
include "cpr.mm"
include "wceq.mm"
include "vex.mm"
include "unieq.mm"
include "suceq.mm"
include "syl.mm"
include "preq12d.mm"
include "prex.mm"
include "fvmpt.mm"
include "ax-mp.mm"

theorem onsetreclem1
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume onsetreclem1.1: |- F = ( x e. _V |-> { U. x , suc U. x } )

  disjoint a x
  disjoint k x
  assert |- ( F ` a ) = { U. a , suc U. a }

  proof
    va
    cv
    #
    cvv
    wcel
    @0
    cF
    cfv
    @0
    cuni
    #
    @1
    csuc
    #
    cpr
    #
    wceq
    va
    vex
    vx
    @0
    vx
    cv
    #
    cuni
    #
    @5
    csuc
    #
    cpr
    @3
    cvv
    cF
    @4
    @0
    wceq
    #
    @5
    @1
    @6
    @2
    @4
    @0
    unieq
    #
    @7
    @5
    @1
    wceq
    @6
    @2
    wceq
    @8
    @5
    @1
    suceq
    syl
    preq12d
    onsetreclem1.1
    @1
    @2
    prex
    fvmpt
    ax-mp
end
