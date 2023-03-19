include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "funfn.mm"
include "eqfnfv2.mm"
include "syl2anb.mm"

theorem eqfunfv
  let vx: setvar x
  let cF: class F
  let cG: class G

  disjoint F x
  disjoint G x
  assert |- ( ( Fun F /\ Fun G ) -> ( F = G <-> ( dom F = dom G /\ A. x e. dom F ( F ` x ) = ( G ` x ) ) ) )

  proof
    cF
    wfun
    cF
    cF
    cdm
    #
    wfn
    cG
    cG
    cdm
    #
    wfn
    cF
    cG
    wceq
    @0
    @1
    wceq
    vx
    cv
    #
    cF
    cfv
    @2
    cG
    cfv
    wceq
    vx
    @0
    wral
    wa
    wb
    cG
    wfun
    cF
    funfn
    cG
    funfn
    vx
    @0
    @1
    cF
    cG
    eqfnfv2
    syl2anb
end
