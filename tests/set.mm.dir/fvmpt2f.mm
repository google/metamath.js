include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "weq.mm"
include "csbeq1.mm"
include "csbid.mm"
include "syl6eq.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "fvmptg.mm"

theorem fvmpt2f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume fvmpt2f.0: |- F/_ x A


  assert |- ( ( x e. A /\ B e. C ) -> ( ( x e. A |-> B ) ` x ) = B )

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
    cC
    vx
    cA
    cB
    cmpt
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
    vx
    vy
    cA
    cB
    @2
    fvmpt2f.0
    vy
    cA
    nfcv
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
    cbvmptf
    fvmptg
end
