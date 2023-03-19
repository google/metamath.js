include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "chash.mm"
include "com.mm"
include "cres.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "ccrd.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "ccom.mm"
include "wf1o.mm"
include "hashgval2.mm"
include "hashgf1o.mm"
include "weq.mm"
include "sneq.mm"
include "pweq.mm"
include "xpeq12d.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "ackbij1.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "f1opwfi.mm"
include "f1oco.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "wcel.mm"
include "wral.mm"
include "inss2.mm"
include "wf.mm"
include "f1of.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbir.mm"
include "rspec.mm"
include "sseldi.mm"
include "wa.mm"
include "snfi.mm"
include "cdm.mm"
include "cnvimass.mm"
include "dmhashres.mm"
include "sseqtri.mm"
include "con0.mm"
include "onfin2.mm"
include "eqsstri.mm"
include "sstri.mm"
include "simpr.mm"
include "pwfi.mm"
include "sylib.mm"
include "xpfi.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "ficardom.mm"
include "syl.mm"
include "fvres.mm"
include "hashcard.mm"
include "c1st.mm"
include "wdisj.mm"
include "xp1st.mm"
include "elsni.mm"
include "rgen.mm"
include "rgenw.mm"
include "invdisj.mm"
include "mp1i.mm"
include "hashiun.mm"
include "sseli.mm"
include "wf1.mm"
include "wss.mm"
include "f1of1.mm"
include "inss1.mm"
include "elpwid.mm"
include "f1ores.mm"
include "adantl.mm"
include "cc.mm"
include "hashcl.mm"
include "nn0cn.mm"
include "3syl.mm"
include "fsumf1o.mm"
include "cmul.mm"
include "c1.mm"
include "sselda.mm"
include "ffvelrni.mm"
include "hashxp.mm"
include "hashsng.mm"
include "hashpw.mm"
include "f1ocnvfv2.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "2cn.mm"
include "expcl.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "sumeq2dv.mm"
include "mpteq2ia.mm"
include "wtru.mm"
include "eqidd.mm"
include "fmptco.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "trud.mm"
include "3eqtr4i.mm"
include "f1oeq1.mm"
include "mpbi.mm"

theorem ackbijnn
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  assume ackbijnn.1: |- F = ( x e. ( ~P NN0 i^i Fin ) |-> sum_ y e. x ( 2 ^ y ) )

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- F : ( ~P NN0 i^i Fin ) -1-1-onto-> NN0

  proof
    cn0
    cpw
    #
    cfn
    cin
    #
    cn0
    chash
    com
    cres
    #
    vz
    com
    cpw
    #
    cfn
    cin
    #
    vw
    vz
    cv
    #
    vw
    cv
    #
    csn
    #
    @6
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    #
    cmpt
    #
    vx
    @1
    @2
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cmpt
    #
    ccom
    #
    ccom
    #
    wf1o
    #
    @1
    cn0
    cF
    wf1o
    #
    com
    cn0
    @2
    wf1o
    #
    @1
    com
    @17
    wf1o
    #
    @19
    vx
    @2
    vx
    hashgval2
    hashgf1o
    #
    @4
    com
    @12
    wf1o
    @1
    @4
    @16
    wf1o
    #
    @22
    vx
    vy
    @12
    vz
    vx
    @4
    @11
    vy
    @14
    vy
    cv
    #
    csn
    #
    @25
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    vz
    vx
    weq
    #
    @10
    @29
    ccrd
    @30
    @10
    vy
    @5
    @28
    ciun
    @29
    vw
    vy
    @5
    @9
    @28
    vw
    vy
    weq
    @7
    @26
    @8
    @27
    @6
    @25
    sneq
    @6
    @25
    pweq
    xpeq12d
    cbviunv
    vy
    @5
    @14
    @28
    iuneq1
    syl5eq
    fveq2d
    cbvmptv
    ackbij1
    cn0
    com
    @13
    wf1o
    #
    @24
    @21
    @31
    @23
    com
    cn0
    @2
    f1ocnv
    ax-mp
    #
    cn0
    com
    @13
    vx
    f1opwfi
    ax-mp
    #
    @1
    @4
    com
    @12
    @16
    f1oco
    mp2an
    @1
    com
    cn0
    @2
    @17
    f1oco
    mp2an
    @18
    cF
    wceq
    @19
    @20
    wb
    vx
    @1
    vw
    @15
    @9
    ciun
    #
    ccrd
    cfv
    #
    @2
    cfv
    #
    cmpt
    #
    vx
    @1
    @14
    c2
    @25
    cexp
    co
    #
    vy
    csu
    #
    cmpt
    @18
    cF
    vx
    @1
    @36
    @39
    @14
    @1
    wcel
    #
    @36
    @35
    chash
    cfv
    #
    @34
    chash
    cfv
    #
    @39
    @40
    @35
    com
    wcel
    #
    @36
    @41
    wceq
    @40
    @34
    cfn
    wcel
    #
    @43
    @40
    @15
    cfn
    wcel
    @9
    cfn
    wcel
    #
    vw
    @15
    wral
    @44
    @40
    @4
    cfn
    @15
    @3
    cfn
    inss2
    @15
    @4
    wcel
    #
    vx
    @1
    @46
    vx
    @1
    wral
    @1
    @4
    @16
    wf
    #
    @24
    @47
    @33
    @1
    @4
    @16
    f1of
    ax-mp
    vx
    @1
    @4
    @15
    @16
    @16
    eqid
    fmpt
    mpbir
    rspec
    #
    sseldi
    #
    @40
    @45
    vw
    @15
    @40
    @6
    @15
    wcel
    #
    wa
    #
    @7
    cfn
    wcel
    @8
    cfn
    wcel
    #
    @45
    @6
    snfi
    @51
    @6
    cfn
    wcel
    @52
    @51
    @15
    cfn
    @6
    @15
    com
    cfn
    @15
    @2
    cdm
    com
    @2
    @14
    cnvimass
    com
    dmhashres
    sseqtri
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    #
    sstri
    @40
    @50
    simpr
    sseldi
    @6
    pwfi
    sylib
    @7
    @8
    xpfi
    sylancr
    #
    ralrimiva
    vw
    @15
    @9
    iunfi
    syl2anc
    #
    @34
    ficardom
    syl
    #
    @35
    com
    chash
    fvres
    syl
    @40
    @44
    @41
    @42
    wceq
    @55
    @34
    hashcard
    syl
    @40
    @42
    @15
    @9
    chash
    cfv
    #
    vw
    csu
    @14
    @25
    @13
    cfv
    #
    csn
    #
    @58
    cpw
    #
    cxp
    #
    chash
    cfv
    #
    vy
    csu
    @39
    @40
    vw
    @15
    @9
    @49
    @54
    @5
    c1st
    cfv
    #
    @6
    wceq
    #
    vz
    @9
    wral
    #
    vw
    @15
    wral
    vw
    @15
    @9
    wdisj
    @40
    @65
    vw
    @15
    @64
    vz
    @9
    @5
    @9
    wcel
    @63
    @7
    wcel
    @64
    @5
    @7
    @8
    xp1st
    @63
    @6
    elsni
    syl
    rgen
    rgenw
    vw
    vz
    @15
    @9
    @63
    invdisj
    mp1i
    hashiun
    @40
    @15
    @57
    @14
    @62
    vw
    vy
    @13
    @14
    cres
    #
    @58
    @6
    @58
    wceq
    #
    @9
    @61
    chash
    @67
    @7
    @59
    @8
    @60
    @6
    @58
    sneq
    @6
    @58
    pweq
    xpeq12d
    fveq2d
    @1
    cfn
    @14
    @0
    cfn
    inss2
    sseli
    @40
    cn0
    com
    @13
    wf1
    #
    @14
    cn0
    wss
    @14
    @15
    @66
    wf1o
    @31
    @68
    @32
    cn0
    com
    @13
    f1of1
    ax-mp
    @40
    @14
    cn0
    @1
    @0
    @14
    @0
    cfn
    inss1
    sseli
    elpwid
    #
    cn0
    com
    @14
    @13
    f1ores
    sylancr
    @25
    @14
    wcel
    #
    @25
    @66
    cfv
    @58
    wceq
    @40
    @25
    @14
    @13
    fvres
    adantl
    @51
    @45
    @57
    cn0
    wcel
    @57
    cc
    wcel
    @54
    @9
    hashcl
    @57
    nn0cn
    3syl
    fsumf1o
    @40
    @14
    @62
    @38
    vy
    @40
    @70
    wa
    #
    @62
    @59
    chash
    cfv
    #
    @60
    chash
    cfv
    #
    cmul
    co
    #
    c1
    @38
    cmul
    co
    @38
    @71
    @59
    cfn
    wcel
    @60
    cfn
    wcel
    #
    @62
    @74
    wceq
    @58
    snfi
    @71
    @58
    cfn
    wcel
    #
    @75
    @71
    com
    cfn
    @58
    @53
    @71
    @25
    cn0
    wcel
    #
    @58
    com
    wcel
    #
    @40
    @14
    cn0
    @25
    @69
    sselda
    #
    cn0
    com
    @25
    @13
    @31
    cn0
    com
    @13
    wf
    @32
    cn0
    com
    @13
    f1of
    ax-mp
    ffvelrni
    syl
    #
    sseldi
    #
    @58
    pwfi
    sylib
    @59
    @60
    hashxp
    sylancr
    @71
    @72
    c1
    @73
    @38
    cmul
    @71
    @78
    @72
    c1
    wceq
    @80
    @58
    com
    hashsng
    syl
    @71
    @73
    c2
    @58
    chash
    cfv
    #
    cexp
    co
    #
    @38
    @71
    @76
    @73
    @83
    wceq
    @81
    @58
    hashpw
    syl
    @71
    @82
    @25
    c2
    cexp
    @71
    @58
    @2
    cfv
    #
    @82
    @25
    @71
    @78
    @84
    @82
    wceq
    @80
    @58
    com
    chash
    fvres
    syl
    @71
    @21
    @77
    @84
    @25
    wceq
    @23
    @79
    com
    cn0
    @25
    @2
    f1ocnvfv2
    sylancr
    eqtr3d
    oveq2d
    eqtrd
    oveq12d
    @71
    @38
    @71
    c2
    cc
    wcel
    @77
    @38
    cc
    wcel
    2cn
    @79
    c2
    @25
    expcl
    sylancr
    mulid2d
    3eqtrd
    sumeq2dv
    3eqtrd
    3eqtrd
    mpteq2ia
    @18
    @37
    wceq
    wtru
    vx
    vy
    @1
    com
    @35
    @25
    @2
    cfv
    @36
    @17
    @2
    @40
    @43
    wtru
    @56
    adantl
    wtru
    vx
    vz
    @1
    @4
    @15
    @11
    @35
    @16
    @12
    @40
    @46
    wtru
    @48
    adantl
    wtru
    @16
    eqidd
    wtru
    @12
    eqidd
    @5
    @15
    wceq
    @10
    @34
    ccrd
    vw
    @5
    @15
    @9
    iuneq1
    fveq2d
    fmptco
    wtru
    vy
    com
    cn0
    @2
    @21
    com
    cn0
    @2
    wf
    wtru
    @23
    com
    cn0
    @2
    f1of
    mp1i
    feqmptd
    @25
    @35
    @2
    fveq2
    fmptco
    trud
    ackbijnn.1
    3eqtr4i
    @1
    cn0
    @18
    cF
    f1oeq1
    ax-mp
    mpbi
end
