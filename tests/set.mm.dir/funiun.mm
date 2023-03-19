include "wfun.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cop.mm"
include "csn.mm"
include "ciun.mm"
include "wfn.mm"
include "wceq.mm"
include "funfn.mm"
include "dffn5.mm"
include "sylbb.mm"
include "fvex.mm"
include "dfmpt.mm"
include "syl6eq.mm"

theorem funiun
  let vx: setvar x
  let cF: class F

  disjoint F x
  assert |- ( Fun F -> F = U_ x e. dom F { <. x , ( F ` x ) >. } )

  proof
    cF
    wfun
    #
    cF
    vx
    cF
    cdm
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    vx
    @1
    @2
    @3
    cop
    csn
    ciun
    @0
    cF
    @1
    wfn
    cF
    @4
    wceq
    cF
    funfn
    vx
    @1
    cF
    dffn5
    sylbb
    vx
    @1
    @3
    @2
    cF
    fvex
    dfmpt
    syl6eq
end
