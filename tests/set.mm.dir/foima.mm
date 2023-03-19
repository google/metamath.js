include "wfo.mm"
include "cdm.mm"
include "cima.mm"
include "crn.mm"
include "imadmrn.mm"
include "wf.mm"
include "wceq.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "imaeq2d.mm"
include "forn.mm"
include "3eqtr3a.mm"

theorem foima
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B -> ( F " A ) = B )

  proof
    cA
    cB
    cF
    wfo
    #
    cF
    cF
    cdm
    #
    cima
    cF
    crn
    cF
    cA
    cima
    cB
    cF
    imadmrn
    @0
    @1
    cA
    cF
    @0
    cA
    cB
    cF
    wf
    @1
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
    imaeq2d
    cA
    cB
    cF
    forn
    3eqtr3a
end
