include "cv.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "wss.mm"
include "cab.mm"
include "df-pw.mm"
include "wex.mm"
include "wb.mm"
include "wal.mm"
include "axpow2.mm"
include "bm1.3ii.mm"
include "abeq2.mm"
include "exbii.mm"
include "mpbir.mm"
include "issetri.mm"
include "eqeltri.mm"
include "vtocl.mm"

theorem pwex
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zfpowcl.1: |- A e. _V


  assert |- ~P A e. _V

  proof
    vz
    cv
    #
    cpw
    #
    cvv
    wcel
    cA
    cpw
    #
    cvv
    wcel
    vz
    cA
    zfpowcl.1
    @0
    cA
    wceq
    @1
    @2
    cvv
    @0
    cA
    pweq
    eleq1d
    @1
    vy
    cv
    #
    @0
    wss
    #
    vy
    cab
    #
    cvv
    vy
    @0
    df-pw
    vx
    @5
    vx
    cv
    #
    @5
    wceq
    #
    vx
    wex
    @3
    @6
    wcel
    @4
    wb
    vy
    wal
    #
    vx
    wex
    @4
    vx
    vy
    vz
    vx
    vy
    axpow2
    bm1.3ii
    @7
    @8
    vx
    @4
    vy
    @6
    abeq2
    exbii
    mpbir
    issetri
    eqeltri
    vtocl
end
