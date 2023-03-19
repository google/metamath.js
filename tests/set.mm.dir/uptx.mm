include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "wceq.mm"
include "wex.mm"
include "wmo.mm"
include "wreu.mm"
include "cuni.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "ctx.mm"
include "eqid.mm"
include "txcnmpt.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "wf.mm"
include "cnf.mm"
include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "crn.mm"
include "wss.mm"
include "cvv.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "a1i.mm"
include "ffvelrn.mm"
include "opelxpi.mm"
include "syl2an.mm"
include "anandirs.mm"
include "fmptd.mm"
include "syl.mm"
include "frn.mm"
include "fnco.mm"
include "syl3anc.mm"
include "fvco3.mm"
include "sylan.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "fveq2d.mm"
include "fvres.mm"
include "fvex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "3eqtrrd.mm"
include "eqfnfvd.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "coeq1i.mm"
include "syl6eqr.mm"
include "c2nd.mm"
include "fo2nd.mm"
include "op2nd.mm"
include "jca32.mm"
include "eleq1.mm"
include "coeq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "ctop.mm"
include "cntop2.mm"
include "txuni.mm"
include "unieqi.mm"
include "syl6reqr.mm"
include "feq3d.mm"
include "syl5ib.mm"
include "anim1d.mm"
include "3anass.mm"
include "syl6ibr.mm"
include "alrimiv.mm"
include "weu.mm"
include "cntop1.mm"
include "uniexg.mm"
include "upxp.mm"
include "eumo.mm"
include "moim.mm"
include "df-reu.mm"
include "eu5.mm"
include "bitri.mm"
include "sylanbrc.mm"

theorem uptx
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vz: setvar z
  assume uptx.1: |- T = ( R tX S )
  assume uptx.2: |- X = U. R
  assume uptx.3: |- Y = U. S
  assume uptx.4: |- Z = ( X X. Y )
  assume uptx.5: |- P = ( 1st |` Z )
  assume uptx.6: |- Q = ( 2nd |` Z )

  disjoint F h
  disjoint G h
  disjoint P h
  disjoint Q h
  disjoint R h
  disjoint T h
  disjoint S h
  disjoint U h
  disjoint X h
  disjoint Y h
  disjoint h x
  disjoint h z
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G x
  disjoint G z
  disjoint R x
  disjoint S x
  disjoint U x
  disjoint U z
  disjoint X x
  disjoint X z
  disjoint Y x
  disjoint Y z
  assert |- ( ( F e. ( U Cn R ) /\ G e. ( U Cn S ) ) -> E! h e. ( U Cn T ) ( F = ( P o. h ) /\ G = ( Q o. h ) ) )

  proof
    cF
    cU
    cR
    ccn
    co
    wcel
    #
    cG
    cU
    cS
    ccn
    co
    wcel
    #
    wa
    #
    vh
    cv
    #
    cU
    cT
    ccn
    co
    #
    wcel
    #
    cF
    cP
    @3
    ccom
    #
    wceq
    #
    cG
    cQ
    @3
    ccom
    #
    wceq
    #
    wa
    #
    wa
    #
    vh
    wex
    #
    @11
    vh
    wmo
    #
    @10
    vh
    @4
    wreu
    #
    @2
    vx
    cU
    cuni
    #
    vx
    cv
    #
    cF
    cfv
    #
    @16
    cG
    cfv
    #
    cop
    #
    cmpt
    #
    @4
    wcel
    #
    @21
    cF
    cP
    @20
    ccom
    #
    wceq
    #
    cG
    cQ
    @20
    ccom
    #
    wceq
    #
    wa
    #
    wa
    #
    @12
    @2
    @20
    cU
    cR
    cS
    ctx
    co
    #
    ccn
    co
    @4
    vx
    cR
    cS
    cU
    cF
    cG
    @20
    @15
    @15
    eqid
    #
    @20
    eqid
    #
    txcnmpt
    cT
    @28
    cU
    ccn
    uptx.1
    oveq2i
    syl6eleqr
    #
    @2
    @21
    @23
    @25
    @31
    @0
    @15
    cX
    cF
    wf
    #
    @15
    cY
    cG
    wf
    #
    @23
    @1
    cF
    cU
    cR
    @15
    cX
    @29
    uptx.2
    cnf
    #
    cG
    cU
    cS
    @15
    cY
    @29
    uptx.3
    cnf
    #
    @32
    @33
    wa
    #
    cF
    c1st
    cX
    cY
    cxp
    #
    cres
    #
    @20
    ccom
    #
    @22
    @36
    vz
    @15
    cF
    @39
    @32
    cF
    @15
    wfn
    @33
    @15
    cX
    cF
    ffn
    adantr
    @36
    @38
    @37
    wfn
    #
    @20
    @15
    wfn
    #
    @20
    crn
    @37
    wss
    #
    @39
    @15
    wfn
    @40
    @36
    c1st
    cvv
    wfn
    #
    @37
    cvv
    wss
    #
    @40
    cvv
    cvv
    c1st
    wfo
    @43
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @37
    ssv
    #
    cvv
    @37
    c1st
    fnssres
    mp2an
    a1i
    @36
    @15
    @37
    @20
    wf
    #
    @41
    @36
    vx
    @15
    @19
    @37
    @20
    @32
    @33
    @16
    @15
    wcel
    #
    @19
    @37
    wcel
    #
    @32
    @47
    wa
    @17
    cX
    wcel
    @18
    cY
    wcel
    @48
    @33
    @47
    wa
    @15
    cX
    @16
    cF
    ffvelrn
    @15
    cY
    @16
    cG
    ffvelrn
    @17
    @18
    cX
    cY
    opelxpi
    syl2an
    anandirs
    @30
    fmptd
    #
    @15
    @37
    @20
    ffn
    syl
    #
    @36
    @46
    @42
    @49
    @15
    @37
    @20
    frn
    syl
    #
    @37
    @15
    @38
    @20
    fnco
    syl3anc
    @36
    vz
    cv
    #
    @15
    wcel
    #
    wa
    #
    @52
    @39
    cfv
    #
    @52
    @20
    cfv
    #
    @38
    cfv
    #
    @52
    cF
    cfv
    #
    @52
    cG
    cfv
    #
    cop
    #
    @38
    cfv
    #
    @58
    @36
    @46
    @53
    @55
    @57
    wceq
    @49
    @15
    @37
    @52
    @38
    @20
    fvco3
    sylan
    @54
    @56
    @60
    @38
    @53
    @56
    @60
    wceq
    @36
    vx
    @52
    @19
    @60
    @15
    @20
    @16
    @52
    wceq
    @17
    @58
    @18
    @59
    @16
    @52
    cF
    fveq2
    @16
    @52
    cG
    fveq2
    opeq12d
    @30
    @58
    @59
    opex
    fvmpt
    adantl
    #
    fveq2d
    @54
    @61
    @60
    c1st
    cfv
    #
    @58
    @54
    @60
    @37
    wcel
    #
    @61
    @63
    wceq
    @32
    @33
    @53
    @64
    @32
    @53
    wa
    @58
    cX
    wcel
    @59
    cY
    wcel
    @64
    @33
    @53
    wa
    @15
    cX
    @52
    cF
    ffvelrn
    @15
    cY
    @52
    cG
    ffvelrn
    @58
    @59
    cX
    cY
    opelxpi
    syl2an
    anandirs
    #
    @60
    @37
    c1st
    fvres
    syl
    @58
    @59
    @52
    cF
    fvex
    #
    @52
    cG
    fvex
    #
    op1st
    syl6eq
    3eqtrrd
    eqfnfvd
    cP
    @38
    @20
    cP
    c1st
    cZ
    cres
    @38
    uptx.5
    cZ
    @37
    c1st
    uptx.4
    reseq2i
    eqtri
    #
    coeq1i
    syl6eqr
    syl2an
    @0
    @32
    @33
    @25
    @1
    @34
    @35
    @36
    cG
    c2nd
    @37
    cres
    #
    @20
    ccom
    #
    @24
    @36
    vz
    @15
    cG
    @70
    @33
    cG
    @15
    wfn
    @32
    @15
    cY
    cG
    ffn
    adantl
    @36
    @69
    @37
    wfn
    #
    @41
    @42
    @70
    @15
    wfn
    @71
    @36
    c2nd
    cvv
    wfn
    #
    @44
    @71
    cvv
    cvv
    c2nd
    wfo
    @72
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    @45
    cvv
    @37
    c2nd
    fnssres
    mp2an
    a1i
    @50
    @51
    @37
    @15
    @69
    @20
    fnco
    syl3anc
    @54
    @52
    @70
    cfv
    #
    @56
    @69
    cfv
    #
    @60
    @69
    cfv
    #
    @59
    @36
    @46
    @53
    @73
    @74
    wceq
    @49
    @15
    @37
    @52
    @69
    @20
    fvco3
    sylan
    @54
    @56
    @60
    @69
    @62
    fveq2d
    @54
    @75
    @60
    c2nd
    cfv
    #
    @59
    @54
    @64
    @75
    @76
    wceq
    @65
    @60
    @37
    c2nd
    fvres
    syl
    @58
    @59
    @66
    @67
    op2nd
    syl6eq
    3eqtrrd
    eqfnfvd
    cQ
    @69
    @20
    cQ
    c2nd
    cZ
    cres
    @69
    uptx.6
    cZ
    @37
    c2nd
    uptx.4
    reseq2i
    eqtri
    #
    coeq1i
    syl6eqr
    syl2an
    jca32
    @11
    @27
    vh
    @20
    @4
    @3
    @20
    wceq
    #
    @5
    @21
    @10
    @26
    @3
    @20
    @4
    eleq1
    @78
    @7
    @23
    @9
    @25
    @78
    @6
    @22
    cF
    @3
    @20
    cP
    coeq2
    eqeq2d
    @78
    @8
    @24
    cG
    @3
    @20
    cQ
    coeq2
    eqeq2d
    anbi12d
    anbi12d
    spcegv
    sylc
    @2
    @11
    @15
    @37
    @3
    wf
    #
    @7
    @9
    w3a
    #
    wi
    #
    vh
    wal
    @80
    vh
    wmo
    #
    @13
    @2
    @81
    vh
    @2
    @11
    @79
    @10
    wa
    @80
    @2
    @5
    @79
    @10
    @5
    @15
    cT
    cuni
    #
    @3
    wf
    @2
    @79
    @3
    cU
    cT
    @15
    @83
    @29
    @83
    eqid
    cnf
    @2
    @83
    @37
    @3
    @15
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @83
    @37
    wceq
    @1
    cF
    cU
    cR
    cntop2
    cG
    cU
    cS
    cntop2
    @84
    @85
    wa
    @37
    @28
    cuni
    @83
    cR
    cS
    cX
    cY
    uptx.2
    uptx.3
    txuni
    cT
    @28
    uptx.1
    unieqi
    syl6reqr
    syl2an
    feq3d
    syl5ib
    anim1d
    @79
    @7
    @9
    3anass
    syl6ibr
    alrimiv
    @2
    @80
    vh
    weu
    #
    @82
    @2
    @15
    cvv
    wcel
    #
    @32
    @33
    @86
    @0
    @87
    @1
    @0
    cU
    ctop
    wcel
    @87
    cF
    cU
    cR
    cntop1
    cU
    ctop
    uniexg
    syl
    adantr
    @0
    @32
    @1
    @34
    adantr
    @1
    @33
    @0
    @35
    adantl
    @15
    cX
    cY
    cvv
    cP
    cQ
    vh
    cF
    cG
    @68
    @77
    upxp
    syl3anc
    @80
    vh
    eumo
    syl
    @11
    @80
    vh
    moim
    sylc
    @14
    @11
    vh
    weu
    @12
    @13
    wa
    @10
    vh
    @4
    df-reu
    @11
    vh
    eu5
    bitri
    sylanbrc
end
