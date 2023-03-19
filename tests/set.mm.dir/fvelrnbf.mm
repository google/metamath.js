include "wfn.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "fvelrnb.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvrexf.mm"
include "syl6bb.mm"

theorem fvelrnbf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume fvelrnbf.1: |- F/_ x A
  assume fvelrnbf.2: |- F/_ x B
  assume fvelrnbf.3: |- F/_ x F


  assert |- ( F Fn A -> ( B e. ran F <-> E. x e. A ( F ` x ) = B ) )

  proof
    cF
    cA
    wfn
    cB
    cF
    crn
    wcel
    vy
    cv
    #
    cF
    cfv
    #
    cB
    wceq
    #
    vy
    cA
    wrex
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    vy
    cA
    cB
    cF
    fvelrnb
    @2
    @5
    vy
    vx
    cA
    vy
    cA
    nfcv
    fvelrnbf.1
    vx
    @1
    cB
    vx
    @0
    cF
    fvelrnbf.3
    vx
    @0
    nfcv
    nffv
    fvelrnbf.2
    nfeq
    @5
    vy
    nfv
    @0
    @3
    wceq
    @1
    @4
    cB
    @0
    @3
    cF
    fveq2
    eqeq1d
    cbvrexf
    syl6bb
end
