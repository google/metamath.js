include "wfn.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "wrex.mm"
include "wfun.mm"
include "wb.mm"
include "fnfun.mm"
include "elunirn.mm"
include "syl.mm"
include "fndm.mm"
include "rexeqdv.mm"
include "bitrd.mm"

theorem fnunirn
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cI: class I

  disjoint A x
  disjoint I x
  disjoint F x
  assert |- ( F Fn I -> ( A e. U. ran F <-> E. x e. I A e. ( F ` x ) ) )

  proof
    cF
    cI
    wfn
    #
    cA
    cF
    crn
    cuni
    wcel
    #
    cA
    vx
    cv
    cF
    cfv
    wcel
    #
    vx
    cF
    cdm
    #
    wrex
    #
    @2
    vx
    cI
    wrex
    @0
    cF
    wfun
    @1
    @4
    wb
    cI
    cF
    fnfun
    vx
    cA
    cF
    elunirn
    syl
    @0
    @2
    vx
    @3
    cI
    cI
    cF
    fndm
    rexeqdv
    bitrd
end
