include "wcel.mm"
include "crn.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "cab.mm"
include "wsbc.mm"
include "wb.mm"
include "wal.mm"
include "idn1.mm"
include "sbcel12gOLD.mm"
include "e1a.mm"
include "csbconstg.mm"
include "eleq1.mm"
include "bibi1.mm"
include "biimprd.mm"
include "e11.mm"
include "gen11.mm"
include "exbi.mm"
include "sbcexgOLD.mm"
include "bicomd.mm"
include "bitr3.mm"
include "com12.mm"
include "abbi.mm"
include "biimpi.mm"
include "csbabgOLD.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "dfrn3.mm"
include "ax-gen.mm"
include "csbeq2gOLD.mm"
include "e10.mm"
include "biimprcd.mm"
include "in1.mm"

theorem csbrngVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vw: setvar w
  let vy: setvar y


  assert |- ( A e. V -> [_ A / x ]_ ran B = ran [_ A / x ]_ B )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    crn
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    crn
    #
    wceq
    #
    @0
    @2
    vw
    cv
    vy
    cv
    cop
    #
    @3
    wcel
    #
    vw
    wex
    #
    vy
    cab
    #
    wceq
    #
    @4
    @9
    wceq
    #
    @5
    @0
    vx
    cA
    @6
    cB
    wcel
    #
    vw
    wex
    #
    vy
    cab
    #
    csb
    #
    @9
    wceq
    #
    @2
    @15
    wceq
    #
    @10
    @0
    @13
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    @9
    wceq
    #
    @15
    @19
    wceq
    #
    @16
    @0
    @18
    @8
    wb
    #
    vy
    wal
    #
    @20
    @0
    @22
    vy
    @0
    @12
    vx
    cA
    wsbc
    #
    vw
    wex
    #
    @8
    wb
    #
    @25
    @18
    wb
    #
    @22
    @0
    @24
    @7
    wb
    #
    vw
    wal
    @26
    @0
    @28
    vw
    @0
    @24
    vx
    cA
    @6
    csb
    #
    @3
    wcel
    #
    wb
    #
    @30
    @7
    wb
    #
    @28
    @0
    @0
    @31
    @0
    idn1
    #
    vx
    cA
    @6
    cB
    cV
    sbcel12gOLD
    e1a
    @0
    @29
    @6
    wceq
    #
    @32
    @0
    @0
    @34
    @33
    vx
    cA
    @6
    cV
    csbconstg
    e1a
    @29
    @6
    @3
    eleq1
    e1a
    @31
    @28
    @32
    @24
    @30
    @7
    bibi1
    biimprd
    e11
    gen11
    @24
    @7
    vw
    exbi
    e1a
    @0
    @0
    @27
    @33
    @0
    @18
    @25
    @12
    vw
    vx
    cA
    cV
    sbcexgOLD
    bicomd
    e1a
    @27
    @26
    @22
    @25
    @18
    @8
    bitr3
    com12
    e11
    gen11
    @23
    @20
    @18
    @8
    vy
    abbi
    biimpi
    e1a
    @0
    @0
    @21
    @33
    @13
    vx
    vy
    cA
    cV
    csbabgOLD
    e1a
    @20
    @21
    @16
    @19
    @9
    @15
    eqeq2
    biimpd
    e11
    @0
    @0
    @1
    @14
    wceq
    #
    vx
    wal
    @17
    @33
    @35
    vx
    vw
    vy
    cB
    dfrn3
    ax-gen
    vx
    cA
    @1
    @14
    cV
    csbeq2gOLD
    e10
    @16
    @17
    @10
    @15
    @9
    @2
    eqeq2
    biimpd
    e11
    vw
    vy
    @3
    dfrn3
    @11
    @5
    @10
    @4
    @9
    @2
    eqeq2
    biimprcd
    e10
    in1
end
