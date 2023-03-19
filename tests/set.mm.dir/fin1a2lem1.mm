include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "wceq.mm"
include "suceloni.mm"
include "cv.mm"
include "suceq.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem fin1a2lem1
  let vx: setvar x
  let cA: class A
  let cS: class S
  let va: setvar a
  let vb: setvar b
  assume fin1a2lem.a: |- S = ( x e. On |-> suc x )


  assert |- ( A e. On -> ( S ` A ) = suc A )

  proof
    cA
    con0
    wcel
    cA
    csuc
    #
    con0
    wcel
    cA
    cS
    cfv
    @0
    wceq
    cA
    suceloni
    va
    cA
    va
    cv
    #
    csuc
    #
    @0
    con0
    con0
    cS
    @1
    cA
    suceq
    cS
    vx
    con0
    vx
    cv
    #
    csuc
    #
    cmpt
    va
    con0
    @2
    cmpt
    fin1a2lem.a
    vx
    va
    con0
    @4
    @2
    @3
    @1
    suceq
    cbvmptv
    eqtri
    fvmptg
    mpdan
end
