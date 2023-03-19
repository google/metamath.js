include "cv.mm"
include "caov.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1.mm"
include "aoveq123d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfaov.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"

theorem csbaovg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  let vk: setvar k


  assert |- ( A e. D -> [_ A / x ]_ (( B F C )) = (( [_ A / x ]_ B [_ A / x ]_ F [_ A / x ]_ C )) )

  proof
    vx
    vy
    cv
    #
    cB
    cC
    cF
    caov
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
    cC
    csb
    #
    vx
    @0
    cF
    csb
    #
    caov
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
    cC
    csb
    #
    vx
    cA
    cF
    csb
    #
    caov
    #
    wceq
    vy
    cA
    cD
    @0
    cA
    wceq
    #
    @2
    @7
    @6
    @11
    vx
    @0
    cA
    @1
    csbeq1
    @12
    @3
    @8
    @4
    @9
    @5
    @10
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
    vx
    @0
    cA
    cC
    csbeq1
    aoveq123d
    eqeq12d
    vx
    @0
    @1
    @6
    vy
    vex
    vx
    @3
    @4
    @5
    vx
    @0
    cB
    nfcsb1v
    vx
    @0
    cF
    nfcsb1v
    vx
    @0
    cC
    nfcsb1v
    nfaov
    vx
    vy
    weq
    cB
    @3
    cC
    @4
    cF
    @5
    vx
    @0
    cF
    csbeq1a
    vx
    @0
    cB
    csbeq1a
    vx
    @0
    cC
    csbeq1a
    aoveq123d
    csbief
    vtoclg
end
