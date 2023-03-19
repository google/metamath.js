include "wcel.mm"
include "csn.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "cab.mm"
include "wsbc.mm"
include "wb.mm"
include "wal.mm"
include "idn1.mm"
include "sbceqg.mm"
include "e1a.mm"
include "csbconstg.mm"
include "eqeq1.mm"
include "bibi1.mm"
include "biimprd.mm"
include "e11.mm"
include "gen11.mm"
include "abbi.mm"
include "biimpi.mm"
include "csbabgOLD.mm"
include "eqcomd.mm"
include "biimpcd.mm"
include "df-sn.mm"
include "ax-gen.mm"
include "csbeq2gOLD.mm"
include "e10.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "biimprcd.mm"
include "in1.mm"

theorem csbsngVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> [_ A / x ]_ { B } = { [_ A / x ]_ B } )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    csn
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    csn
    #
    wceq
    #
    @0
    @2
    vy
    cv
    #
    @3
    wceq
    #
    vy
    cab
    #
    wceq
    #
    @4
    @8
    wceq
    #
    @5
    @0
    vx
    cA
    @6
    cB
    wceq
    #
    vy
    cab
    #
    csb
    #
    @8
    wceq
    #
    @2
    @13
    wceq
    #
    @9
    @0
    @11
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    @8
    wceq
    #
    @17
    @13
    wceq
    #
    @14
    @0
    @16
    @7
    wb
    #
    vy
    wal
    #
    @18
    @0
    @20
    vy
    @0
    @16
    vx
    cA
    @6
    csb
    #
    @3
    wceq
    #
    wb
    #
    @23
    @7
    wb
    #
    @20
    @0
    @0
    @24
    @0
    idn1
    #
    vx
    cA
    @6
    cB
    cV
    sbceqg
    e1a
    @0
    @22
    @6
    wceq
    #
    @25
    @0
    @0
    @27
    @26
    vx
    cA
    @6
    cV
    csbconstg
    e1a
    @22
    @6
    @3
    eqeq1
    e1a
    @24
    @20
    @25
    @16
    @23
    @7
    bibi1
    biimprd
    e11
    gen11
    @21
    @18
    @16
    @7
    vy
    abbi
    biimpi
    e1a
    @0
    @0
    @19
    @26
    @0
    @13
    @17
    @11
    vx
    vy
    cA
    cV
    csbabgOLD
    eqcomd
    e1a
    @19
    @18
    @14
    @17
    @13
    @8
    eqeq1
    biimpcd
    e11
    @0
    @0
    @1
    @12
    wceq
    #
    vx
    wal
    @15
    @26
    @28
    vx
    vy
    cB
    df-sn
    ax-gen
    vx
    cA
    @1
    @12
    cV
    csbeq2gOLD
    e10
    @14
    @15
    @9
    @13
    @8
    @2
    eqeq2
    biimpd
    e11
    vy
    @3
    df-sn
    @10
    @5
    @9
    @4
    @8
    @2
    eqeq2
    biimprcd
    e10
    in1
end
