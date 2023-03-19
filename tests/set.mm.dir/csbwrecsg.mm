include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "cuni.mm"
include "csb.mm"
include "cwrecs.mm"
include "csbuni.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbcex2.mm"
include "sbc3an.mm"
include "sbcg.mm"
include "sbcan.mm"
include "sbcssg.mm"
include "csbconstg.mm"
include "sseq1d.mm"
include "bitrd.mm"
include "sbcralg.mm"
include "sseq2d.mm"
include "csbpredg.mm"
include "predeq3.mm"
include "syl.mm"
include "eqtrd.mm"
include "3bitrd.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "sbceqg.mm"
include "csbfv12.mm"
include "csbres.mm"
include "reseq12d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "exbidv.mm"
include "abbidv.mm"
include "unieqd.mm"
include "df-wrecs.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbwrecsg
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> [_ A / x ]_ wrecs ( R , D , F ) = wrecs ( [_ A / x ]_ R , [_ A / x ]_ D , [_ A / x ]_ F ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vf
    cv
    #
    vz
    cv
    #
    wfn
    #
    @2
    cD
    wss
    #
    cD
    cR
    vy
    cv
    #
    cpred
    #
    @2
    wss
    #
    vy
    @2
    wral
    #
    wa
    #
    @5
    @1
    cfv
    #
    @1
    @6
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @2
    wral
    #
    w3a
    #
    vz
    wex
    #
    vf
    cab
    #
    cuni
    #
    csb
    #
    @3
    @2
    vx
    cA
    cD
    csb
    #
    wss
    #
    @20
    vx
    cA
    cR
    csb
    #
    @5
    cpred
    #
    @2
    wss
    #
    vy
    @2
    wral
    #
    wa
    #
    @10
    @1
    @23
    cres
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
    vy
    @2
    wral
    #
    w3a
    #
    vz
    wex
    #
    vf
    cab
    #
    cuni
    #
    vx
    cA
    cD
    cR
    cF
    cwrecs
    #
    csb
    @20
    @22
    @28
    cwrecs
    @0
    @19
    vx
    cA
    @17
    csb
    #
    cuni
    @35
    vx
    cA
    @17
    csbuni
    @0
    @37
    @34
    @0
    @37
    @16
    vx
    cA
    wsbc
    #
    vf
    cab
    @34
    @16
    vx
    vf
    cA
    csbab
    @0
    @38
    @33
    vf
    @38
    @15
    vx
    cA
    wsbc
    #
    vz
    wex
    @0
    @33
    @15
    vz
    vx
    cA
    sbcex2
    @0
    @39
    @32
    vz
    @39
    @3
    vx
    cA
    wsbc
    #
    @9
    vx
    cA
    wsbc
    #
    @14
    vx
    cA
    wsbc
    #
    w3a
    @0
    @32
    @3
    @9
    @14
    vx
    cA
    sbc3an
    @0
    @40
    @3
    @41
    @26
    @42
    @31
    @3
    vx
    cA
    cV
    sbcg
    @41
    @4
    vx
    cA
    wsbc
    #
    @8
    vx
    cA
    wsbc
    #
    wa
    @0
    @26
    @4
    @8
    vx
    cA
    sbcan
    @0
    @43
    @21
    @44
    @25
    @0
    @43
    vx
    cA
    @2
    csb
    #
    @20
    wss
    @21
    vx
    cA
    @2
    cD
    cV
    sbcssg
    @0
    @45
    @2
    @20
    vx
    cA
    @2
    cV
    csbconstg
    #
    sseq1d
    bitrd
    @0
    @44
    @7
    vx
    cA
    wsbc
    #
    vy
    @2
    wral
    @25
    @7
    vx
    vy
    cA
    @2
    cV
    sbcralg
    @0
    @47
    @24
    vy
    @2
    @0
    @47
    vx
    cA
    @6
    csb
    #
    @45
    wss
    @48
    @2
    wss
    @24
    vx
    cA
    @6
    @2
    cV
    sbcssg
    @0
    @45
    @2
    @48
    @46
    sseq2d
    @0
    @48
    @23
    @2
    @0
    @48
    @20
    @22
    vx
    cA
    @5
    csb
    #
    cpred
    #
    @23
    vx
    cA
    cD
    cR
    cV
    @5
    csbpredg
    @0
    @49
    @5
    wceq
    @50
    @23
    wceq
    vx
    cA
    @5
    cV
    csbconstg
    @20
    @22
    @49
    @5
    predeq3
    syl
    eqtrd
    #
    sseq1d
    3bitrd
    ralbidv
    bitrd
    anbi12d
    syl5bb
    @0
    @42
    @13
    vx
    cA
    wsbc
    #
    vy
    @2
    wral
    @31
    @13
    vx
    vy
    cA
    @2
    cV
    sbcralg
    @0
    @52
    @30
    vy
    @2
    @0
    @52
    vx
    cA
    @10
    csb
    #
    vx
    cA
    @12
    csb
    #
    wceq
    @30
    vx
    cA
    @10
    @12
    cV
    sbceqg
    @0
    @53
    @10
    @54
    @29
    vx
    cA
    @10
    cV
    csbconstg
    @0
    @54
    vx
    cA
    @11
    csb
    #
    @28
    cfv
    @29
    vx
    cA
    @11
    cF
    csbfv12
    @0
    @55
    @27
    @28
    @0
    @55
    vx
    cA
    @1
    csb
    #
    @48
    cres
    @27
    vx
    cA
    @1
    @6
    csbres
    @0
    @56
    @1
    @48
    @23
    vx
    cA
    @1
    cV
    csbconstg
    @51
    reseq12d
    syl5eq
    fveq2d
    syl5eq
    eqeq12d
    bitrd
    ralbidv
    bitrd
    3anbi123d
    syl5bb
    exbidv
    syl5bb
    abbidv
    syl5eq
    unieqd
    syl5eq
    vx
    cA
    @36
    @18
    vz
    vy
    cD
    cR
    vf
    cF
    df-wrecs
    csbeq2i
    vz
    vy
    @20
    @22
    vf
    @28
    df-wrecs
    3eqtr4g
end
