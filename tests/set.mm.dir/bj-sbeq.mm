include "wceq.mm"
include "wsb.mm"
include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wsbc.mm"
include "dfcleq.mm"
include "sbbii.mm"
include "sbsbc.mm"
include "sbcal.mm"
include "3bitri.mm"
include "cvv.mm"
include "vex.mm"
include "sbcbig.mm"
include "ax-mp.mm"
include "albii.mm"
include "sbcel2.mm"
include "bibi12i.mm"
include "bitr4i.mm"

theorem bj-sbeq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z


  assert |- ( [ y / x ] A = B <-> [_ y / x ]_ A = [_ y / x ]_ B )

  proof
    cA
    cB
    wceq
    #
    vx
    vy
    wsb
    #
    vz
    cv
    #
    vx
    vy
    cv
    #
    cA
    csb
    #
    wcel
    #
    @2
    vx
    @3
    cB
    csb
    #
    wcel
    #
    wb
    #
    vz
    wal
    #
    @4
    @6
    wceq
    @1
    @2
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wb
    #
    vx
    @3
    wsbc
    #
    vz
    wal
    #
    @10
    vx
    @3
    wsbc
    #
    @11
    vx
    @3
    wsbc
    #
    wb
    #
    vz
    wal
    @9
    @1
    @12
    vz
    wal
    #
    vx
    vy
    wsb
    @18
    vx
    @3
    wsbc
    @14
    @0
    @18
    vx
    vy
    vz
    cA
    cB
    dfcleq
    sbbii
    @18
    vx
    vy
    sbsbc
    @12
    vz
    vx
    @3
    sbcal
    3bitri
    @13
    @17
    vz
    @3
    cvv
    wcel
    @13
    @17
    wb
    vy
    vex
    @10
    @11
    vx
    @3
    cvv
    sbcbig
    ax-mp
    albii
    @17
    @8
    vz
    @15
    @5
    @16
    @7
    vx
    @3
    @2
    cA
    sbcel2
    vx
    @3
    @2
    cB
    sbcel2
    bibi12i
    albii
    3bitri
    vz
    @4
    @6
    dfcleq
    bitr4i
end
