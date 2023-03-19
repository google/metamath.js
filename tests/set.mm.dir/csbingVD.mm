include "wcel.mm"
include "cin.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "wsbc.mm"
include "idn1.mm"
include "wal.mm"
include "df-in.mm"
include "ax-gen.mm"
include "spsbc.mm"
include "e10.mm"
include "sbceqg.mm"
include "biimpd.mm"
include "e11.mm"
include "csbabgOLD.mm"
include "e1a.mm"
include "eqeq1.mm"
include "biimprd.mm"
include "wb.mm"
include "sbcangOLD.mm"
include "sbcel2gOLD.mm"
include "pm4.38.mm"
include "ex.mm"
include "bibi1.mm"
include "gen11.mm"
include "abbi.mm"
include "biimpi.mm"
include "eqeq2.mm"
include "biimprcd.mm"
include "in1.mm"

theorem csbingVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y


  assert |- ( A e. B -> [_ A / x ]_ ( C i^i D ) = ( [_ A / x ]_ C i^i [_ A / x ]_ D ) )

  proof
    cA
    cB
    wcel
    #
    vx
    cA
    cC
    cD
    cin
    #
    csb
    #
    vx
    cA
    cC
    csb
    #
    vx
    cA
    cD
    csb
    #
    cin
    #
    wceq
    #
    @0
    @2
    vy
    cv
    #
    @3
    wcel
    #
    @7
    @4
    wcel
    #
    wa
    #
    vy
    cab
    #
    wceq
    #
    @5
    @11
    wceq
    #
    @6
    @0
    @2
    @7
    cC
    wcel
    #
    @7
    cD
    wcel
    #
    wa
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    wceq
    #
    @18
    @11
    wceq
    #
    @12
    @0
    @2
    vx
    cA
    @16
    vy
    cab
    #
    csb
    #
    wceq
    #
    @22
    @18
    wceq
    #
    @19
    @0
    @0
    @1
    @21
    wceq
    #
    vx
    cA
    wsbc
    #
    @23
    @0
    idn1
    #
    @0
    @0
    @25
    vx
    wal
    @26
    @27
    @25
    vx
    vy
    cC
    cD
    df-in
    ax-gen
    @25
    vx
    cA
    cB
    spsbc
    e10
    @0
    @26
    @23
    vx
    cA
    @1
    @21
    cB
    sbceqg
    biimpd
    e11
    @0
    @0
    @24
    @27
    @16
    vx
    vy
    cA
    cB
    csbabgOLD
    e1a
    @23
    @19
    @24
    @2
    @22
    @18
    eqeq1
    biimprd
    e11
    @0
    @17
    @10
    wb
    #
    vy
    wal
    #
    @20
    @0
    @28
    vy
    @0
    @17
    @14
    vx
    cA
    wsbc
    #
    @15
    vx
    cA
    wsbc
    #
    wa
    #
    wb
    #
    @32
    @10
    wb
    #
    @28
    @0
    @0
    @33
    @27
    @14
    @15
    vx
    cA
    cB
    sbcangOLD
    e1a
    @0
    @30
    @8
    wb
    #
    @31
    @9
    wb
    #
    @34
    @0
    @0
    @35
    @27
    vx
    cA
    @7
    cC
    cB
    sbcel2gOLD
    e1a
    @0
    @0
    @36
    @27
    vx
    cA
    @7
    cD
    cB
    sbcel2gOLD
    e1a
    @35
    @36
    @34
    @30
    @31
    @8
    @9
    pm4.38
    ex
    e11
    @33
    @28
    @34
    @17
    @32
    @10
    bibi1
    biimprd
    e11
    gen11
    @29
    @20
    @17
    @10
    vy
    abbi
    biimpi
    e1a
    @19
    @12
    @20
    @2
    @18
    @11
    eqeq1
    biimprd
    e11
    vy
    @3
    @4
    df-in
    @13
    @6
    @12
    @5
    @11
    @2
    eqeq2
    biimprcd
    e10
    in1
end
