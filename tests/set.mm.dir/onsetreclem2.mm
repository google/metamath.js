include "cv.mm"
include "con0.mm"
include "wss.mm"
include "cfv.mm"
include "cuni.mm"
include "csuc.mm"
include "cpr.mm"
include "onsetreclem1.mm"
include "wcel.mm"
include "vex.mm"
include "ssonunii.mm"
include "suceloni.mm"
include "prssi.mm"
include "mpdan.mm"
include "syl.mm"
include "syl5eqss.mm"

theorem onsetreclem2
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume onsetreclem2.1: |- F = ( x e. _V |-> { U. x , suc U. x } )

  disjoint a x
  disjoint k x
  assert |- ( a C_ On -> ( F ` a ) C_ On )

  proof
    va
    cv
    #
    con0
    wss
    #
    @0
    cF
    cfv
    @0
    cuni
    #
    @2
    csuc
    #
    cpr
    #
    con0
    vx
    cF
    va
    onsetreclem2.1
    onsetreclem1
    @1
    @2
    con0
    wcel
    #
    @4
    con0
    wss
    #
    @0
    va
    vex
    ssonunii
    @5
    @3
    con0
    wcel
    @6
    @2
    suceloni
    @2
    @3
    con0
    prssi
    mpdan
    syl
    syl5eqss
end
