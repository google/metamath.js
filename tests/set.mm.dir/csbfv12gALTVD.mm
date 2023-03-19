include "wcel.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "cab.mm"
include "cuni.mm"
include "wsbc.mm"
include "wb.mm"
include "wal.mm"
include "idn1.mm"
include "sbceqg.mm"
include "e1a.mm"
include "csbima12.mm"
include "a1i.mm"
include "csbsng.mm"
include "imaeq2.mm"
include "eqeq1.mm"
include "biimprd.mm"
include "e11.mm"
include "csbconstg.mm"
include "eqeq12.mm"
include "ex.mm"
include "bibi1.mm"
include "gen11.mm"
include "abbi.mm"
include "biimpi.mm"
include "csbab.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "unieq.mm"
include "csbuni.mm"
include "dffv4.mm"
include "ax-gen.mm"
include "wi.mm"
include "csbeq2.mm"
include "e10.mm"
include "biimprcd.mm"
include "in1.mm"

theorem csbfv12gALTVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y


  assert |- ( A e. C -> [_ A / x ]_ ( F ` B ) = ( [_ A / x ]_ F ` [_ A / x ]_ B ) )

  proof
    cA
    cC
    wcel
    #
    vx
    cA
    cB
    cF
    cfv
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cF
    csb
    #
    cfv
    #
    wceq
    #
    @0
    @2
    @4
    @3
    csn
    #
    cima
    #
    vy
    cv
    csn
    #
    wceq
    #
    vy
    cab
    #
    cuni
    #
    wceq
    #
    @5
    @12
    wceq
    #
    @6
    @0
    vx
    cA
    cF
    cB
    csn
    #
    cima
    #
    @9
    wceq
    #
    vy
    cab
    #
    cuni
    #
    csb
    #
    @12
    wceq
    #
    @2
    @20
    wceq
    #
    @13
    @0
    vx
    cA
    @18
    csb
    #
    cuni
    #
    @12
    wceq
    #
    @20
    @24
    wceq
    #
    @21
    @0
    @23
    @11
    wceq
    #
    @25
    @0
    @17
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    @11
    wceq
    #
    @23
    @29
    wceq
    #
    @27
    @0
    @28
    @10
    wb
    #
    vy
    wal
    #
    @30
    @0
    @32
    vy
    @0
    @28
    vx
    cA
    @16
    csb
    #
    vx
    cA
    @9
    csb
    #
    wceq
    #
    wb
    #
    @36
    @10
    wb
    #
    @32
    @0
    @0
    @37
    @0
    idn1
    #
    vx
    cA
    @16
    @9
    cC
    sbceqg
    e1a
    @0
    @34
    @8
    wceq
    #
    @35
    @9
    wceq
    #
    @38
    @0
    @34
    @4
    vx
    cA
    @15
    csb
    #
    cima
    #
    wceq
    #
    @43
    @8
    wceq
    #
    @40
    @0
    @0
    @44
    @39
    @44
    @0
    vx
    cA
    @15
    cF
    csbima12
    a1i
    e1a
    @0
    @42
    @7
    wceq
    #
    @45
    @0
    @0
    @46
    @39
    vx
    cA
    cB
    cC
    csbsng
    e1a
    @42
    @7
    @4
    imaeq2
    e1a
    @44
    @40
    @45
    @34
    @43
    @8
    eqeq1
    biimprd
    e11
    @0
    @0
    @41
    @39
    vx
    cA
    @9
    cC
    csbconstg
    e1a
    @40
    @41
    @38
    @34
    @8
    @35
    @9
    eqeq12
    ex
    e11
    @37
    @32
    @38
    @28
    @36
    @10
    bibi1
    biimprd
    e11
    gen11
    @33
    @30
    @28
    @10
    vy
    abbi
    biimpi
    e1a
    @0
    @0
    @31
    @39
    @31
    @0
    @17
    vx
    vy
    cA
    csbab
    a1i
    e1a
    @30
    @31
    @27
    @29
    @11
    @23
    eqeq2
    biimpd
    e11
    @23
    @11
    unieq
    e1a
    @0
    @0
    @26
    @39
    @26
    @0
    vx
    cA
    @18
    csbuni
    a1i
    e1a
    @25
    @26
    @21
    @24
    @12
    @20
    eqeq2
    biimpd
    e11
    @0
    @0
    @1
    @19
    wceq
    #
    vx
    wal
    #
    @22
    @39
    @47
    vx
    vy
    cB
    cF
    dffv4
    ax-gen
    @48
    @22
    wi
    @0
    vx
    cA
    @1
    @19
    csbeq2
    a1i
    e10
    @21
    @22
    @13
    @20
    @12
    @2
    eqeq2
    biimpd
    e11
    vy
    @3
    @4
    dffv4
    @14
    @6
    @13
    @5
    @12
    @2
    eqeq2
    biimprcd
    e10
    in1
end
