include "wfun.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "funfv.mm"
include "wrel.mm"
include "wceq.mm"
include "funrel.mm"
include "relimasn.mm"
include "syl.mm"
include "unieqd.mm"
include "eqtrd.mm"

theorem funfv2
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint A y
  disjoint F y
  assert |- ( Fun F -> ( F ` A ) = U. { y | A F y } )

  proof
    cF
    wfun
    #
    cA
    cF
    cfv
    cF
    cA
    csn
    cima
    #
    cuni
    cA
    vy
    cv
    cF
    wbr
    vy
    cab
    #
    cuni
    cA
    cF
    funfv
    @0
    @1
    @2
    @0
    cF
    wrel
    @1
    @2
    wceq
    cF
    funrel
    vy
    cA
    cF
    relimasn
    syl
    unieqd
    eqtrd
end
