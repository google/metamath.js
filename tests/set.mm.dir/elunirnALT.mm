include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "cima.mm"
include "wfun.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "imadmrn.mm"
include "unieqi.mm"
include "eleq2i.mm"
include "eluniima.mm"
include "syl5bbr.mm"

theorem elunirnALT
  let vx: setvar x
  let cA: class A
  let cF: class F

  disjoint A x
  disjoint F x
  assert |- ( Fun F -> ( A e. U. ran F <-> E. x e. dom F A e. ( F ` x ) ) )

  proof
    cA
    cF
    crn
    #
    cuni
    #
    wcel
    cA
    cF
    cF
    cdm
    #
    cima
    #
    cuni
    #
    wcel
    cF
    wfun
    cA
    vx
    cv
    cF
    cfv
    wcel
    vx
    @2
    wrex
    @4
    @1
    cA
    @3
    @0
    cF
    imadmrn
    unieqi
    eleq2i
    vx
    @2
    cA
    cF
    eluniima
    syl5bbr
end
