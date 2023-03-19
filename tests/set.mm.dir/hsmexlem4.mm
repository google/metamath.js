include "cv.mm"
include "com.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "wral.mm"
include "crnk.mm"
include "c0.mm"
include "cima.mm"
include "cep.mm"
include "coi.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "imaeq2d.mm"
include "oieq2.mm"
include "syl.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "eleq12d.mm"
include "ralbidv.mm"
include "weq.mm"
include "cpw.mm"
include "char.mm"
include "con0.mm"
include "wss.mm"
include "cwdom.mm"
include "wbr.mm"
include "crn.mm"
include "imassrn.mm"
include "cr1.mm"
include "cuni.mm"
include "wf.mm"
include "rankf.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "cvv.mm"
include "vex.mm"
include "ituni0.mm"
include "imaeq2i.mm"
include "wfun.mm"
include "ffun.mm"
include "wdomimag.mm"
include "mp2an.mm"
include "cdom.mm"
include "csn.mm"
include "ctc.mm"
include "sneq.mm"
include "fveq2d.mm"
include "raleqdv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "wi.mm"
include "snex.mm"
include "tcid.mm"
include "vsnid.mm"
include "sselii.mm"
include "breq1.mm"
include "rspcv.mm"
include "domwdom.mm"
include "3syl.mm"
include "wdomtr.mm"
include "sylancr.mm"
include "syl5eqbr.mm"
include "eqid.mm"
include "hsmexlem1.mm"
include "hsmexlem7.mm"
include "syl6eleqr.mm"
include "rgen.mm"
include "wa.mm"
include "nfra1.mm"
include "nfv.mm"
include "nfan.mm"
include "cxp.mm"
include "ciun.mm"
include "ituniiun.mm"
include "imaiun.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "ad2antll.mm"
include "hsmexlem9.mm"
include "ad2antrl.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "r1elssi.mm"
include "sselda.mm"
include "snssi.mm"
include "tcss.mm"
include "tcel.mm"
include "mp1i.mm"
include "sstrd.mm"
include "ssralv.mm"
include "mpan9.mm"
include "sylanbrc.mm"
include "adantll.mm"
include "simpll.mm"
include "fveq1d.mm"
include "eleq1d.mm"
include "sylc.mm"
include "fvex.mm"
include "funimaex.mm"
include "elpw.mm"
include "mpbir.mm"
include "jctil.mm"
include "ralrimiva.mm"
include "hsmexlem3.mm"
include "syl21anc.mm"
include "syl5eqel.mm"
include "hsmexlem8.mm"
include "eleqtrrd.mm"
include "expr.mm"
include "ralrimi.mm"
include "expcom.mm"
include "finds1.mm"
include "r19.21bi.mm"

theorem hsmexlem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cU: class U
  let cH: class H
  let cO: class O
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume hsmexlem4.x: |- X e. _V
  assume hsmexlem4.h: |- H = ( rec ( ( z e. _V |-> ( har ` ~P ( X X. z ) ) ) , ( har ` ~P X ) ) |` _om )
  assume hsmexlem4.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )
  assume hsmexlem4.s: |- S = { a e. U. ( R1 " On ) | A. b e. ( TC ` { a } ) b ~<_ X }
  assume hsmexlem4.o: |- O = OrdIso ( _E , ( rank " ( ( U ` d ) ` c ) ) )

  disjoint a c
  disjoint a d
  disjoint H a
  disjoint c d
  disjoint H c
  disjoint H d
  disjoint S c
  disjoint S d
  disjoint U c
  disjoint U d
  disjoint a b
  disjoint a z
  disjoint X a
  disjoint b z
  disjoint X b
  disjoint X z
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a e
  disjoint a f
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint H e
  disjoint H f
  disjoint O e
  disjoint S e
  disjoint S f
  disjoint U f
  disjoint b e
  disjoint b f
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f x
  disjoint f y
  disjoint f z
  assert |- ( ( c e. _om /\ d e. S ) -> dom O e. ( H ` c ) )

  proof
    vc
    cv
    #
    com
    wcel
    cO
    cdm
    #
    @0
    cH
    cfv
    #
    wcel
    #
    vd
    cS
    @3
    vd
    cS
    wral
    crnk
    c0
    vd
    cv
    #
    cU
    cfv
    #
    cfv
    #
    cima
    #
    cep
    coi
    #
    cdm
    #
    c0
    cH
    cfv
    #
    wcel
    #
    vd
    cS
    wral
    crnk
    ve
    cv
    #
    @5
    cfv
    #
    cima
    #
    cep
    coi
    #
    cdm
    #
    @12
    cH
    cfv
    #
    wcel
    #
    vd
    cS
    wral
    #
    crnk
    @12
    csuc
    #
    @5
    cfv
    #
    cima
    #
    cep
    coi
    #
    cdm
    #
    @20
    cH
    cfv
    #
    wcel
    #
    vd
    cS
    wral
    #
    vc
    ve
    @0
    c0
    wceq
    #
    @3
    @11
    vd
    cS
    @28
    @1
    @9
    @2
    @10
    @28
    cO
    @8
    @28
    cO
    crnk
    @0
    @5
    cfv
    #
    cima
    #
    cep
    coi
    #
    @8
    hsmexlem4.o
    @28
    @30
    @7
    wceq
    @31
    @8
    wceq
    @28
    @29
    @6
    crnk
    @0
    c0
    @5
    fveq2
    imaeq2d
    @30
    @7
    cep
    oieq2
    syl
    syl5eq
    dmeqd
    @0
    c0
    cH
    fveq2
    eleq12d
    ralbidv
    vc
    ve
    weq
    #
    @3
    @18
    vd
    cS
    @32
    @1
    @16
    @2
    @17
    @32
    cO
    @15
    @32
    cO
    @31
    @15
    hsmexlem4.o
    @32
    @30
    @14
    wceq
    @31
    @15
    wceq
    @32
    @29
    @13
    crnk
    @0
    @12
    @5
    fveq2
    imaeq2d
    @30
    @14
    cep
    oieq2
    syl
    syl5eq
    dmeqd
    @0
    @12
    cH
    fveq2
    eleq12d
    ralbidv
    @0
    @20
    wceq
    #
    @3
    @26
    vd
    cS
    @33
    @1
    @24
    @2
    @25
    @33
    cO
    @23
    @33
    cO
    @31
    @23
    hsmexlem4.o
    @33
    @30
    @22
    wceq
    @31
    @23
    wceq
    @33
    @29
    @21
    crnk
    @0
    @20
    @5
    fveq2
    imaeq2d
    @30
    @22
    cep
    oieq2
    syl
    syl5eq
    dmeqd
    @0
    @20
    cH
    fveq2
    eleq12d
    ralbidv
    @11
    vd
    cS
    @4
    cS
    wcel
    #
    @9
    cX
    cpw
    char
    cfv
    #
    @10
    @34
    @7
    con0
    wss
    @7
    cX
    cwdom
    wbr
    @9
    @35
    wcel
    @7
    crnk
    crn
    #
    con0
    crnk
    @6
    imassrn
    cr1
    con0
    cima
    cuni
    #
    con0
    crnk
    wf
    #
    @36
    con0
    wss
    rankf
    @37
    con0
    crnk
    frn
    ax-mp
    #
    sstri
    @34
    @7
    crnk
    @4
    cima
    #
    cX
    cwdom
    @6
    @4
    crnk
    @4
    cvv
    wcel
    #
    @6
    @4
    wceq
    vd
    vex
    #
    vx
    vy
    @4
    cU
    cvv
    hsmexlem4.u
    ituni0
    ax-mp
    imaeq2i
    @34
    @40
    @4
    cwdom
    wbr
    #
    @4
    cX
    cwdom
    wbr
    #
    @40
    cX
    cwdom
    wbr
    crnk
    wfun
    #
    @41
    @43
    @38
    @45
    rankf
    @37
    con0
    crnk
    ffun
    ax-mp
    #
    @42
    @4
    crnk
    cvv
    wdomimag
    mp2an
    @34
    vb
    cv
    #
    cX
    cdom
    wbr
    #
    vb
    @4
    csn
    #
    ctc
    cfv
    #
    wral
    #
    @4
    cX
    cdom
    wbr
    #
    @44
    @34
    @4
    @37
    wcel
    #
    @51
    @48
    vb
    va
    cv
    #
    csn
    #
    ctc
    cfv
    #
    wral
    #
    @51
    va
    @4
    @37
    cS
    va
    vd
    weq
    #
    @48
    vb
    @56
    @50
    @58
    @55
    @49
    ctc
    @54
    @4
    sneq
    fveq2d
    raleqdv
    hsmexlem4.s
    elrab2
    simprbi
    #
    @4
    @50
    wcel
    @51
    @52
    wi
    @49
    @50
    @4
    @49
    cvv
    wcel
    @49
    @50
    wss
    @4
    snex
    #
    @49
    cvv
    tcid
    ax-mp
    vd
    vsnid
    #
    sselii
    @48
    @52
    vb
    @4
    @50
    @47
    @4
    cX
    cdom
    breq1
    rspcv
    ax-mp
    @4
    cX
    domwdom
    3syl
    #
    @40
    @4
    cX
    wdomtr
    sylancr
    syl5eqbr
    @7
    cX
    @8
    @8
    eqid
    hsmexlem1
    sylancr
    vz
    cH
    cX
    hsmexlem4.h
    hsmexlem7
    syl6eleqr
    rgen
    @19
    @12
    com
    wcel
    #
    @27
    @19
    @63
    wa
    @26
    vd
    cS
    @19
    @63
    vd
    @18
    vd
    cS
    nfra1
    @63
    vd
    nfv
    nfan
    @19
    @63
    @34
    @26
    @19
    @63
    @34
    wa
    #
    wa
    #
    @24
    cX
    @17
    cxp
    cpw
    char
    cfv
    #
    @25
    @65
    @24
    vf
    @4
    crnk
    @12
    vf
    cv
    #
    cU
    cfv
    #
    cfv
    #
    cima
    #
    ciun
    #
    cep
    coi
    #
    cdm
    #
    @66
    @23
    @72
    @22
    @71
    wceq
    @23
    @72
    wceq
    @22
    crnk
    vf
    @4
    @69
    ciun
    #
    cima
    @71
    @21
    @74
    crnk
    @41
    @21
    @74
    wceq
    @42
    vx
    vy
    @4
    @12
    cU
    cvv
    vf
    hsmexlem4.u
    ituniiun
    ax-mp
    imaeq2i
    vf
    crnk
    @4
    @69
    imaiun
    eqtri
    @22
    @71
    cep
    oieq2
    ax-mp
    dmeqi
    @65
    @44
    @17
    con0
    wcel
    #
    @70
    con0
    cpw
    wcel
    #
    @70
    cep
    coi
    #
    cdm
    #
    @17
    wcel
    #
    wa
    #
    vf
    @4
    wral
    @73
    @66
    wcel
    @34
    @44
    @19
    @63
    @62
    ad2antll
    @63
    @75
    @19
    @34
    vz
    cH
    cX
    ve
    hsmexlem4.h
    hsmexlem9
    ad2antrl
    @65
    @80
    vf
    @4
    @65
    @67
    @4
    wcel
    #
    wa
    #
    @79
    @76
    @82
    @67
    cS
    wcel
    #
    @19
    @79
    @64
    @81
    @83
    @19
    @34
    @81
    @83
    @63
    @34
    @81
    wa
    @67
    @37
    wcel
    @48
    vb
    @67
    csn
    #
    ctc
    cfv
    #
    wral
    #
    @83
    @34
    @4
    @37
    @67
    @34
    @53
    @4
    @37
    wss
    cS
    @37
    @4
    cS
    @57
    va
    @37
    crab
    @37
    hsmexlem4.s
    @57
    va
    @37
    ssrab2
    eqsstri
    sseli
    @4
    r1elssi
    syl
    sselda
    @34
    @51
    @81
    @86
    @59
    @81
    @85
    @50
    wss
    @51
    @86
    wi
    @81
    @85
    @4
    ctc
    cfv
    #
    @50
    @81
    @84
    @4
    wss
    @85
    @87
    wss
    @67
    @4
    snssi
    @4
    @84
    @42
    tcss
    syl
    @4
    @49
    wcel
    @87
    @50
    wss
    @81
    @61
    @49
    @4
    @60
    tcel
    mp1i
    sstrd
    @48
    vb
    @85
    @50
    ssralv
    syl
    mpan9
    @57
    @86
    va
    @67
    @37
    cS
    va
    vf
    weq
    #
    @48
    vb
    @56
    @85
    @88
    @55
    @84
    ctc
    @54
    @67
    sneq
    fveq2d
    raleqdv
    hsmexlem4.s
    elrab2
    sylanbrc
    adantll
    adantll
    @19
    @64
    @81
    simpll
    @18
    @79
    vd
    @67
    cS
    vd
    vf
    weq
    #
    @16
    @78
    @17
    @89
    @15
    @77
    @89
    @14
    @70
    wceq
    @15
    @77
    wceq
    @89
    @13
    @69
    crnk
    @89
    @12
    @5
    @68
    @4
    @67
    cU
    fveq2
    fveq1d
    imaeq2d
    @14
    @70
    cep
    oieq2
    syl
    dmeqd
    eleq1d
    rspcv
    sylc
    @76
    @70
    con0
    wss
    @70
    @36
    con0
    crnk
    @69
    imassrn
    @39
    sstri
    @70
    con0
    @45
    @70
    cvv
    wcel
    @46
    crnk
    @69
    @12
    @68
    fvex
    funimaex
    ax-mp
    elpw
    mpbir
    jctil
    ralrimiva
    @4
    @70
    @17
    cX
    @77
    @72
    vf
    @77
    eqid
    @72
    eqid
    hsmexlem3
    syl21anc
    syl5eqel
    @63
    @25
    @66
    wceq
    @19
    @34
    vz
    cH
    cX
    ve
    hsmexlem4.h
    hsmexlem8
    ad2antrl
    eleqtrrd
    expr
    ralrimi
    expcom
    finds1
    r19.21bi
end
