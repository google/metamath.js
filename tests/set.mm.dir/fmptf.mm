include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "csb.mm"
include "wf.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "cmpt.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fmpt.mm"
include "bitri.mm"

theorem fmptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  assume fmptf.1: |- F/_ x B
  assume fmptf.2: |- F = ( x e. A |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  assert |- ( A. x e. A C e. B <-> F : A --> B )

  proof
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    vx
    vy
    cv
    #
    cC
    csb
    #
    cB
    wcel
    #
    vy
    cA
    wral
    cA
    cB
    cF
    wf
    @0
    @3
    vx
    vy
    cA
    @0
    vy
    nfv
    vx
    @2
    cB
    vx
    @1
    cC
    nfcsb1v
    #
    fmptf.1
    nfel
    vx
    cv
    @1
    wceq
    cC
    @2
    cB
    vx
    @1
    cC
    csbeq1a
    #
    eleq1d
    cbvral
    vy
    cA
    cB
    @2
    cF
    cF
    vx
    cA
    cC
    cmpt
    vy
    cA
    @2
    cmpt
    fmptf.2
    vx
    vy
    cA
    cC
    @2
    vy
    cC
    nfcv
    @4
    @5
    cbvmpt
    eqtri
    fmpt
    bitri
end
