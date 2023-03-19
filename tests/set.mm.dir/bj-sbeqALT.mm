include "wceq.mm"
include "cv.mm"
include "csb.mm"
include "nfcsb1v.mm"
include "nfeq.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eqeq12d.mm"
include "sbie.mm"

theorem bj-sbeqALT
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  assert |- ( [ y / x ] A = B <-> [_ y / x ]_ A = [_ y / x ]_ B )

  proof
    cA
    cB
    wceq
    vx
    vy
    cv
    #
    cA
    csb
    #
    vx
    @0
    cB
    csb
    #
    wceq
    vx
    vy
    vx
    @1
    @2
    vx
    @0
    cA
    nfcsb1v
    vx
    @0
    cB
    nfcsb1v
    nfeq
    vx
    vy
    weq
    cA
    @1
    cB
    @2
    vx
    @0
    cA
    csbeq1a
    vx
    @0
    cB
    csbeq1a
    eqeq12d
    sbie
end
