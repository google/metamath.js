include "cv.mm"
include "csb.mm"
include "weq.mm"
include "csbeq1.mm"
include "csbid.mm"
include "syl6eq.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fvmpti.mm"

theorem fvmpt2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let cD: class D
  assume mptrcl.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint D y
  disjoint F y
  assert |- ( x e. A -> ( F ` x ) = ( _I ` B ) )

  proof
    vy
    vx
    cv
    #
    vx
    vy
    cv
    #
    cB
    csb
    #
    cB
    cA
    cF
    vy
    vx
    weq
    @2
    vx
    @0
    cB
    csb
    cB
    vx
    @1
    @0
    cB
    csbeq1
    vx
    cB
    csbid
    syl6eq
    cF
    vx
    cA
    cB
    cmpt
    vy
    cA
    @2
    cmpt
    mptrcl.1
    vx
    vy
    cA
    cB
    @2
    vy
    cB
    nfcv
    vx
    @1
    cB
    nfcsb1v
    vx
    @1
    cB
    csbeq1a
    cbvmpt
    eqtri
    fvmpti
end
