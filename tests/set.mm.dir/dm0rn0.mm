include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "crn.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wn.mm"
include "alnex.mm"
include "excom.mm"
include "xchbinx.mm"
include "bitr4i.mm"
include "noel.mm"
include "nbn.mm"
include "albii.mm"
include "3bitr3i.mm"
include "abeq1.mm"
include "3bitr4i.mm"
include "df-dm.mm"
include "eqeq1i.mm"
include "dfrn2.mm"

theorem dm0rn0
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( dom A = (/) <-> ran A = (/) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vy
    wex
    #
    vx
    cab
    #
    c0
    wceq
    #
    @2
    vx
    wex
    #
    vy
    cab
    #
    c0
    wceq
    #
    cA
    cdm
    #
    c0
    wceq
    cA
    crn
    #
    c0
    wceq
    @3
    @0
    c0
    wcel
    #
    wb
    #
    vx
    wal
    #
    @6
    @1
    c0
    wcel
    #
    wb
    #
    vy
    wal
    #
    @5
    @8
    @3
    wn
    #
    vx
    wal
    #
    @6
    wn
    #
    vy
    wal
    #
    @13
    @16
    @18
    @6
    vy
    wex
    #
    wn
    @20
    @18
    @3
    vx
    wex
    @21
    @3
    vx
    alnex
    @2
    vx
    vy
    excom
    xchbinx
    @6
    vy
    alnex
    bitr4i
    @17
    @12
    vx
    @11
    @3
    @0
    noel
    nbn
    albii
    @19
    @15
    vy
    @14
    @6
    @1
    noel
    nbn
    albii
    3bitr3i
    @3
    vx
    c0
    abeq1
    @6
    vy
    c0
    abeq1
    3bitr4i
    @9
    @4
    c0
    vx
    vy
    cA
    df-dm
    eqeq1i
    @10
    @7
    c0
    vx
    vy
    cA
    dfrn2
    eqeq1i
    3bitr4i
end
