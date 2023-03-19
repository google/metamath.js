include "ctb.mm"
include "wcel.mm"
include "wf1o.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "cqtop.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wral.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "f1ocnv.mm"
include "f1ofun.mm"
include "syl.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "crn.mm"
include "df-rn.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5eqr.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "dfss3.mm"
include "wrex.mm"
include "inss1.mm"
include "simprl.mm"
include "sseldi.mm"
include "elqtop2.mm"
include "sylan2.mm"
include "ad3antrrr.mm"
include "mpbid.mm"
include "simprd.mm"
include "inss2.mm"
include "elpwid.mm"
include "imass2.mm"
include "elpwg.mm"
include "mpbird.mm"
include "elind.mm"
include "wfn.mm"
include "simp-4r.mm"
include "f1ofn.mm"
include "ad2antrr.mm"
include "sstrd.mm"
include "simprr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eleq2.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "funimass2.mm"
include "wf1.mm"
include "f1of1.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "f1imacnv.mm"
include "eqeltrd.mm"
include "mpbir2and.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "sselda.mm"
include "adantr.mm"
include "f1ocnvfv2.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "impbid.mm"
include "eluni2.mm"
include "3bitr4g.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitr4d.mm"
include "eltg.mm"
include "cvv.mm"
include "ovex.mm"
include "mp1i.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "ctopon.mm"
include "tgtopon.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "elqtop3.mm"
include "unitg.mm"
include "ax-mp.mm"
include "simpl.mm"
include "selpw.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "sspwuni.mm"
include "sylib.mm"
include "syl5eqss.mm"
include "sseld.mm"
include "syl6ib.mm"
include "pm4.71rd.mm"
include "eqrdv.mm"

theorem tgqtop
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume qtopcmp.1: |- X = U. J


  assert |- ( ( J e. TopBases /\ F : X -1-1-onto-> Y ) -> ( ( topGen ` J ) qTop F ) = ( topGen ` ( J qTop F ) ) )

  proof
    cJ
    ctb
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    wa
    #
    vx
    cJ
    ctg
    cfv
    #
    cF
    cqtop
    co
    #
    cJ
    cF
    cqtop
    co
    #
    ctg
    cfv
    #
    @2
    vx
    cv
    #
    cY
    wss
    #
    cF
    ccnv
    #
    @7
    cima
    #
    @3
    wcel
    #
    wa
    #
    @8
    @7
    @6
    wcel
    #
    wa
    @7
    @4
    wcel
    #
    @13
    @2
    @8
    @11
    @13
    @2
    @8
    wa
    #
    @10
    cJ
    @10
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    @7
    @5
    @7
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    @11
    @13
    @15
    @19
    vy
    cv
    #
    @9
    cfv
    #
    @18
    wcel
    #
    vy
    @7
    wral
    #
    @23
    @15
    @9
    wfun
    #
    @7
    @9
    cdm
    #
    wss
    @19
    @27
    wb
    @1
    @28
    @0
    @8
    @1
    cY
    cX
    @9
    wf1o
    #
    @28
    cX
    cY
    cF
    f1ocnv
    #
    cY
    cX
    @9
    f1ofun
    syl
    ad2antlr
    @15
    @7
    cY
    @29
    @2
    @8
    simpr
    #
    @15
    @29
    cF
    crn
    #
    cY
    cF
    df-rn
    @15
    cX
    cY
    cF
    wfo
    #
    @33
    cY
    wceq
    @1
    @34
    @0
    @8
    cX
    cY
    cF
    f1ofo
    #
    ad2antlr
    cX
    cY
    cF
    forn
    syl
    syl5eqr
    sseqtr4d
    vy
    @7
    @18
    @9
    funimass4
    syl2anc
    @23
    @24
    @22
    wcel
    #
    vy
    @7
    wral
    @15
    @27
    vy
    @7
    @22
    dfss3
    @15
    @36
    @26
    vy
    @7
    @15
    @24
    @7
    wcel
    #
    wa
    #
    @24
    vz
    cv
    #
    wcel
    #
    vz
    @21
    wrex
    #
    @25
    vw
    cv
    #
    wcel
    #
    vw
    @17
    wrex
    #
    @36
    @26
    @38
    @41
    @44
    @38
    @40
    @44
    vz
    @21
    @38
    @39
    @21
    wcel
    #
    @40
    wa
    #
    wa
    #
    @9
    @39
    cima
    #
    @17
    wcel
    @25
    @48
    wcel
    #
    @44
    @47
    cJ
    @16
    @48
    @47
    @39
    cY
    wss
    #
    @48
    cJ
    wcel
    #
    @47
    @39
    @5
    wcel
    #
    @50
    @51
    wa
    #
    @47
    @21
    @5
    @39
    @5
    @20
    inss1
    @38
    @45
    @40
    simprl
    #
    sseldi
    @2
    @52
    @53
    wb
    #
    @8
    @37
    @46
    @1
    @0
    @34
    @55
    @35
    @39
    cF
    cJ
    ctb
    cX
    cY
    qtopcmp.1
    elqtop2
    sylan2
    ad3antrrr
    mpbid
    simprd
    #
    @47
    @48
    @16
    wcel
    #
    @48
    @10
    wss
    #
    @47
    @39
    @7
    wss
    @58
    @47
    @39
    @7
    @47
    @21
    @20
    @39
    @5
    @20
    inss2
    @54
    sseldi
    elpwid
    #
    @39
    @7
    @9
    imass2
    syl
    @47
    @51
    @57
    @58
    wb
    @56
    @48
    @10
    cJ
    elpwg
    syl
    mpbird
    elind
    @47
    @9
    cY
    wfn
    #
    @50
    @40
    @49
    @47
    @30
    @60
    @47
    @1
    @30
    @0
    @1
    @8
    @37
    @46
    simp-4r
    @31
    syl
    cY
    cX
    @9
    f1ofn
    syl
    @47
    @39
    @7
    cY
    @59
    @15
    @8
    @37
    @46
    @32
    ad2antrr
    sstrd
    @38
    @45
    @40
    simprr
    cY
    @39
    @9
    @24
    fnfvima
    syl3anc
    @43
    @49
    vw
    @48
    @17
    @42
    @48
    @25
    eleq2
    rspcev
    syl2anc
    rexlimdvaa
    @38
    @43
    @41
    vw
    @17
    @38
    @42
    @17
    wcel
    #
    @43
    wa
    #
    wa
    #
    cF
    @42
    cima
    #
    @21
    wcel
    @24
    @64
    wcel
    #
    @41
    @63
    @5
    @20
    @64
    @63
    @64
    @5
    wcel
    #
    @64
    cY
    wss
    #
    @9
    @64
    cima
    #
    cJ
    wcel
    #
    @63
    @64
    @7
    cY
    @63
    cF
    wfun
    #
    @42
    @10
    wss
    @64
    @7
    wss
    #
    @63
    @1
    @70
    @0
    @1
    @8
    @37
    @62
    simp-4r
    #
    cX
    cY
    cF
    f1ofun
    syl
    @63
    @42
    @10
    @63
    @17
    @16
    @42
    cJ
    @16
    inss2
    @38
    @61
    @43
    simprl
    #
    sseldi
    elpwid
    @42
    @7
    cF
    funimass2
    syl2anc
    #
    @15
    @8
    @37
    @62
    @32
    ad2antrr
    sstrd
    @63
    @68
    @42
    cJ
    @63
    cX
    cY
    cF
    wf1
    #
    @42
    cX
    wss
    #
    @68
    @42
    wceq
    @63
    @1
    @75
    @72
    cX
    cY
    cF
    f1of1
    syl
    @63
    @42
    cJ
    wcel
    #
    @76
    @63
    @17
    cJ
    @42
    cJ
    @16
    inss1
    @73
    sseldi
    #
    @77
    @42
    cJ
    cuni
    #
    cX
    @42
    cJ
    elssuni
    qtopcmp.1
    syl6sseqr
    syl
    #
    cX
    cY
    @42
    cF
    f1imacnv
    syl2anc
    @78
    eqeltrd
    @2
    @66
    @67
    @69
    wa
    wb
    #
    @8
    @37
    @62
    @1
    @0
    @34
    @81
    @35
    @64
    cF
    cJ
    ctb
    cX
    cY
    qtopcmp.1
    elqtop2
    sylan2
    ad3antrrr
    mpbir2and
    @63
    @71
    @64
    @20
    wcel
    @74
    @64
    @7
    vx
    vex
    elpw2
    sylibr
    elind
    @63
    @25
    cF
    cfv
    #
    @24
    @64
    @63
    @1
    @24
    cY
    wcel
    #
    @82
    @24
    wceq
    @72
    @38
    @83
    @62
    @15
    @7
    cY
    @24
    @32
    sselda
    adantr
    cX
    cY
    @24
    cF
    f1ocnvfv2
    syl2anc
    @63
    cF
    cX
    wfn
    #
    @76
    @43
    @82
    @64
    wcel
    @2
    @84
    @8
    @37
    @62
    @1
    @84
    @0
    cX
    cY
    cF
    f1ofn
    adantl
    ad3antrrr
    @80
    @38
    @61
    @43
    simprr
    cX
    @42
    cF
    @25
    fnfvima
    syl3anc
    eqeltrrd
    @40
    @65
    vz
    @64
    @21
    @39
    @64
    @24
    eleq2
    rspcev
    syl2anc
    rexlimdvaa
    impbid
    vz
    @24
    @21
    eluni2
    vw
    @25
    @17
    eluni2
    3bitr4g
    ralbidva
    syl5bb
    bitr4d
    @0
    @11
    @19
    wb
    @1
    @8
    @10
    cJ
    ctb
    eltg
    ad2antrr
    @5
    cvv
    wcel
    #
    @13
    @23
    wb
    @15
    cJ
    cF
    cqtop
    ovex
    #
    @7
    @5
    cvv
    eltg
    mp1i
    3bitr4d
    pm5.32da
    @2
    @3
    cX
    ctopon
    cfv
    #
    wcel
    @34
    @14
    @12
    wb
    @2
    @3
    @79
    ctopon
    cfv
    #
    @87
    @0
    @3
    @88
    wcel
    @1
    cJ
    tgtopon
    adantr
    cX
    @79
    ctopon
    qtopcmp.1
    fveq2i
    syl6eleqr
    @1
    @34
    @0
    @35
    adantl
    @7
    cF
    @3
    cX
    cY
    elqtop3
    syl2anc
    @2
    @13
    @8
    @2
    @13
    @7
    cY
    cpw
    #
    wcel
    #
    @8
    @2
    @6
    @89
    @7
    @2
    @6
    cuni
    #
    cY
    wss
    @6
    @89
    wss
    @2
    @91
    @5
    cuni
    #
    cY
    @85
    @91
    @92
    wceq
    @86
    @5
    cvv
    unitg
    ax-mp
    @2
    @5
    @89
    wss
    @92
    cY
    wss
    @2
    vx
    @5
    @89
    @2
    @7
    @5
    wcel
    #
    @8
    @10
    cJ
    wcel
    #
    wa
    #
    @90
    @1
    @0
    @34
    @93
    @95
    wb
    @35
    @7
    cF
    cJ
    ctb
    cX
    cY
    qtopcmp.1
    elqtop2
    sylan2
    @95
    @8
    @90
    @8
    @94
    simpl
    vx
    cY
    selpw
    #
    sylibr
    syl6bi
    ssrdv
    @5
    cY
    sspwuni
    sylib
    syl5eqss
    @6
    cY
    sspwuni
    sylibr
    sseld
    @96
    syl6ib
    pm4.71rd
    3bitr4d
    eqrdv
end
