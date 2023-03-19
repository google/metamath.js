include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cshi.mm"
include "co.mm"
include "csn.mm"
include "cima.mm"
include "cio.mm"
include "cmin.mm"
include "cfv.mm"
include "shftfib.mm"
include "eleq2d.mm"
include "iotabidv.mm"
include "dffv3.mm"
include "3eqtr4g.mm"

theorem shftval
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( F shift A ) ` B ) = ( F ` ( B - A ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    vx
    cv
    #
    cF
    cA
    cshi
    co
    #
    cB
    csn
    cima
    #
    wcel
    #
    vx
    cio
    @1
    cF
    cB
    cA
    cmin
    co
    #
    csn
    cima
    #
    wcel
    #
    vx
    cio
    cB
    @2
    cfv
    @5
    cF
    cfv
    @0
    @4
    @7
    vx
    @0
    @3
    @6
    @1
    cA
    cB
    cF
    shftfval.1
    shftfib
    eleq2d
    iotabidv
    vx
    cB
    @2
    dffv3
    vx
    @5
    cF
    dffv3
    3eqtr4g
end
