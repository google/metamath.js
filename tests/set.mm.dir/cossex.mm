include "wcel.mm"
include "ccoss.mm"
include "ccnv.mm"
include "ccom.mm"
include "cvv.mm"
include "dfcoss3.mm"
include "cnvexg.mm"
include "coexg.mm"
include "mpdan.mm"
include "syl5eqel.mm"

theorem cossex
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ,~ A e. _V )

  proof
    cA
    cV
    wcel
    #
    cA
    ccoss
    cA
    cA
    ccnv
    #
    ccom
    #
    cvv
    cA
    dfcoss3
    @0
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    cA
    cV
    cnvexg
    cA
    @1
    cV
    cvv
    coexg
    mpdan
    syl5eqel
end
