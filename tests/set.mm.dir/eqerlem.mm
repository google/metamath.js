include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wsbc.mm"
include "csb.mm"
include "brabsb.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfeq.mm"
include "weq.mm"
include "nfv.mm"
include "csbie.mm"
include "csbeq1.mm"
include "syl5eqr.mm"
include "eqeq2d.mm"
include "sbciegf.mm"
include "ax-mp.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "bitri.mm"

theorem eqerlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let vv: setvar v
  assume eqer.1: |- ( x = y -> A = B )
  assume eqer.2: |- R = { <. x , y >. | A = B }

  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint B x
  disjoint v x
  disjoint B v
  assert |- ( z R w <-> [_ z / x ]_ A = [_ w / x ]_ A )

  proof
    vz
    cv
    #
    vw
    cv
    #
    cR
    wbr
    cA
    cB
    wceq
    #
    vy
    @1
    wsbc
    #
    vx
    @0
    wsbc
    #
    vx
    @0
    cA
    csb
    #
    vx
    @1
    cA
    csb
    #
    wceq
    #
    @2
    vx
    vy
    @0
    @1
    cR
    eqer.2
    brabsb
    @0
    cvv
    wcel
    @4
    @7
    wb
    vz
    vex
    @3
    @7
    vx
    @0
    cvv
    vx
    @5
    @6
    vx
    @0
    cA
    nfcsb1v
    vx
    @1
    cA
    nfcsb1v
    nfeq
    @3
    cA
    @6
    wceq
    #
    vx
    vz
    weq
    #
    @7
    @1
    cvv
    wcel
    @3
    @8
    wb
    vw
    vex
    @2
    @8
    vy
    @1
    cvv
    @8
    vy
    nfv
    vy
    vw
    weq
    #
    cB
    @6
    cA
    @10
    cB
    vx
    vy
    cv
    #
    cA
    csb
    @6
    vx
    @11
    cA
    cB
    vy
    vex
    eqer.1
    csbie
    vx
    @11
    @1
    cA
    csbeq1
    syl5eqr
    eqeq2d
    sbciegf
    ax-mp
    @9
    cA
    @5
    @6
    vx
    @0
    cA
    csbeq1a
    eqeq1d
    syl5bb
    sbciegf
    ax-mp
    bitri
end
