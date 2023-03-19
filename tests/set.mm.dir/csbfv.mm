include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "csbfv2g.mm"
include "csbvarg.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "fvprc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem csbfv
  let vx: setvar x
  let cA: class A
  let cF: class F

  disjoint F x
  assert |- [_ A / x ]_ ( F ` x ) = ( F ` A )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    csb
    #
    cA
    cF
    cfv
    #
    wceq
    @0
    @3
    vx
    cA
    @1
    csb
    #
    cF
    cfv
    @4
    vx
    cA
    @1
    cvv
    cF
    csbfv2g
    @0
    @5
    cA
    cF
    vx
    cA
    cvv
    csbvarg
    fveq2d
    eqtrd
    @0
    wn
    @3
    c0
    @4
    vx
    cA
    @2
    csbprc
    cA
    cF
    fvprc
    eqtr4d
    pm2.61i
end
