include "cv.mm"
include "csb.mm"
include "csbeq1.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fvmptg.mm"

theorem fvmpts
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vy: setvar y
  assume fvmpts.1: |- F = ( x e. C |-> B )

  disjoint C x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint C y
  assert |- ( ( A e. C /\ [_ A / x ]_ B e. V ) -> ( F ` A ) = [_ A / x ]_ B )

  proof
    vy
    cA
    vx
    vy
    cv
    #
    cB
    csb
    #
    vx
    cA
    cB
    csb
    cC
    cV
    cF
    vx
    @0
    cA
    cB
    csbeq1
    cF
    vx
    cC
    cB
    cmpt
    vy
    cC
    @1
    cmpt
    fvmpts.1
    vx
    vy
    cC
    cB
    @1
    vy
    cB
    nfcv
    vx
    @0
    cB
    nfcsb1v
    vx
    @0
    cB
    csbeq1a
    cbvmpt
    eqtri
    fvmptg
end
