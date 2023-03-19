include "cv.mm"
include "con0.mm"
include "wcel.mm"
include "cuni.mm"
include "csuc.mm"
include "cpr.mm"
include "cfv.mm"
include "wceq.mm"
include "wo.mm"
include "word.mm"
include "eloni.mm"
include "orduniorsuc.mm"
include "syl.mm"
include "vex.mm"
include "elpr.mm"
include "sylibr.mm"
include "onsetreclem1.mm"
include "syl6eleqr.mm"

theorem onsetreclem3
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume onsetreclem3.1: |- F = ( x e. _V |-> { U. x , suc U. x } )

  disjoint a x
  disjoint k x
  assert |- ( a e. On -> a e. ( F ` a ) )

  proof
    va
    cv
    #
    con0
    wcel
    #
    @0
    @0
    cuni
    #
    @2
    csuc
    #
    cpr
    #
    @0
    cF
    cfv
    @1
    @0
    @2
    wceq
    @0
    @3
    wceq
    wo
    #
    @0
    @4
    wcel
    @1
    @0
    word
    @5
    @0
    eloni
    @0
    orduniorsuc
    syl
    @0
    @2
    @3
    va
    vex
    elpr
    sylibr
    vx
    cF
    va
    onsetreclem3.1
    onsetreclem1
    syl6eleqr
end
