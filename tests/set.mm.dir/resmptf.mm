include "wss.mm"
include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "cres.mm"
include "resmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "reseq1i.mm"
include "3eqtr4g.mm"

theorem resmptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume resmptf.a: |- F/_ x A
  assume resmptf.b: |- F/_ x B


  assert |- ( B C_ A -> ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C ) )

  proof
    cB
    cA
    wss
    vy
    cA
    vx
    vy
    cv
    #
    cC
    csb
    #
    cmpt
    #
    cB
    cres
    vy
    cB
    @1
    cmpt
    vx
    cA
    cC
    cmpt
    #
    cB
    cres
    vx
    cB
    cC
    cmpt
    vy
    cA
    cB
    @1
    resmpt
    @3
    @2
    cB
    vx
    vy
    cA
    cC
    @1
    resmptf.a
    vy
    cA
    nfcv
    vy
    cC
    nfcv
    #
    vx
    @0
    cC
    nfcsb1v
    #
    vx
    @0
    cC
    csbeq1a
    #
    cbvmptf
    reseq1i
    vx
    vy
    cB
    cC
    @1
    resmptf.b
    vy
    cB
    nfcv
    @4
    @5
    @6
    cbvmptf
    3eqtr4g
end
