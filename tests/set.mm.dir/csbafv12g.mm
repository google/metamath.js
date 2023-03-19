include "cv.mm"
include "cafv.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1.mm"
include "afveq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfafv.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"

theorem csbafv12g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vk: setvar k


  assert |- ( A e. V -> [_ A / x ]_ ( F ''' B ) = ( [_ A / x ]_ F ''' [_ A / x ]_ B ) )

  proof
    vx
    vy
    cv
    #
    cB
    cF
    cafv
    #
    csb
    #
    vx
    @0
    cB
    csb
    #
    vx
    @0
    cF
    csb
    #
    cafv
    #
    wceq
    vx
    cA
    @1
    csb
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cF
    csb
    #
    cafv
    #
    wceq
    vy
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @6
    @5
    @9
    vx
    @0
    cA
    @1
    csbeq1
    @10
    @3
    @7
    @4
    @8
    vx
    @0
    cA
    cF
    csbeq1
    vx
    @0
    cA
    cB
    csbeq1
    afveq12d
    eqeq12d
    vx
    @0
    @1
    @5
    vy
    vex
    vx
    @3
    @4
    vx
    @0
    cF
    nfcsb1v
    vx
    @0
    cB
    nfcsb1v
    nfafv
    vx
    vy
    weq
    cB
    @3
    cF
    @4
    vx
    @0
    cF
    csbeq1a
    vx
    @0
    cB
    csbeq1a
    afveq12d
    csbief
    vtoclg
end
