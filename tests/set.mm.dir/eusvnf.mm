include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "weu.mm"
include "wex.mm"
include "wnfc.mm"
include "euex.mm"
include "csb.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "vex.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "spcgf.mm"
include "ax-mp.mm"
include "eqtr3d.mm"
include "alrimivv.mm"
include "sbnfc2.mm"
include "sylibr.mm"
include "exlimiv.mm"
include "syl.mm"

theorem eusvnf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( E! y A. x y = A -> F/_ x A )

  proof
    vy
    cv
    #
    cA
    wceq
    #
    vx
    wal
    #
    vy
    weu
    @2
    vy
    wex
    vx
    cA
    wnfc
    #
    @2
    vy
    euex
    @2
    @3
    vy
    @2
    vx
    vz
    cv
    #
    cA
    csb
    #
    vx
    vw
    cv
    #
    cA
    csb
    #
    wceq
    #
    vw
    wal
    vz
    wal
    @3
    @2
    @8
    vz
    vw
    @2
    @0
    @5
    @7
    @4
    cvv
    wcel
    @2
    @0
    @5
    wceq
    #
    wi
    vz
    vex
    @1
    @9
    vx
    @4
    cvv
    vx
    @4
    nfcv
    vx
    @0
    @5
    vx
    @4
    cA
    nfcsb1v
    nfeq2
    vx
    cv
    #
    @4
    wceq
    cA
    @5
    @0
    vx
    @4
    cA
    csbeq1a
    eqeq2d
    spcgf
    ax-mp
    @6
    cvv
    wcel
    @2
    @0
    @7
    wceq
    #
    wi
    vw
    vex
    @1
    @11
    vx
    @6
    cvv
    vx
    @6
    nfcv
    vx
    @0
    @7
    vx
    @6
    cA
    nfcsb1v
    nfeq2
    @10
    @6
    wceq
    cA
    @7
    @0
    vx
    @6
    cA
    csbeq1a
    eqeq2d
    spcgf
    ax-mp
    eqtr3d
    alrimivv
    vx
    vz
    vw
    cA
    sbnfc2
    sylibr
    exlimiv
    syl
end
