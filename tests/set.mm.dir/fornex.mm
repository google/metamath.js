include "wfo.mm"
include "wcel.mm"
include "cvv.mm"
include "cdm.mm"
include "crn.mm"
include "wfun.mm"
include "fofun.mm"
include "funrnex.mm"
include "syl5com.mm"
include "wf.mm"
include "wceq.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "eleq1d.mm"
include "forn.mm"
include "3imtr3d.mm"
include "com12.mm"

theorem fornex
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A e. C -> ( F : A -onto-> B -> B e. _V ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cA
    cC
    wcel
    #
    cB
    cvv
    wcel
    #
    @0
    cF
    cdm
    #
    cC
    wcel
    #
    cF
    crn
    #
    cvv
    wcel
    #
    @1
    @2
    @0
    cF
    wfun
    @4
    @6
    cA
    cB
    cF
    fofun
    cC
    cF
    funrnex
    syl5com
    @0
    @3
    cA
    cC
    @0
    cA
    cB
    cF
    wf
    @3
    cA
    wceq
    cA
    cB
    cF
    fof
    cA
    cB
    cF
    fdm
    syl
    eleq1d
    @0
    @5
    cB
    cvv
    cA
    cB
    cF
    forn
    eleq1d
    3imtr3d
    com12
end
