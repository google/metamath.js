include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "dffr2.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "iniseg.mm"
include "ax-mp.mm"
include "ineq2i.mm"
include "dfrab3.mm"
include "eqtr4i.mm"
include "eqeq1i.mm"
include "rexbii.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitr4i.mm"

theorem dffr3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint R z
  assert |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x ( x i^i ( `' R " { y } ) ) = (/) ) )

  proof
    cA
    cR
    wfr
    vx
    cv
    #
    cA
    wss
    @0
    c0
    wne
    wa
    #
    vz
    cv
    vy
    cv
    #
    cR
    wbr
    #
    vz
    @0
    crab
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    @1
    @0
    cR
    ccnv
    @2
    csn
    cima
    #
    cin
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    vx
    vy
    vz
    cA
    cR
    dffr2
    @12
    @7
    vx
    @11
    @6
    @1
    @10
    @5
    vy
    @0
    @9
    @4
    c0
    @9
    @0
    @3
    vz
    cab
    #
    cin
    @4
    @8
    @13
    @0
    @2
    cvv
    wcel
    @8
    @13
    wceq
    vy
    vex
    vz
    cR
    @2
    cvv
    iniseg
    ax-mp
    ineq2i
    @3
    vz
    @0
    dfrab3
    eqtr4i
    eqeq1i
    rexbii
    imbi2i
    albii
    bitr4i
end
