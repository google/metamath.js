include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cdir.mm"
include "cdm.mm"
include "cv.mm"
include "wf.mm"
include "ctail.mm"
include "crn.mm"
include "cfm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cxp.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "filnetlem3.mm"
include "simpri.mm"
include "simprd.mm"
include "c2nd.mm"
include "cres.mm"
include "cvv.mm"
include "f2ndres.mm"
include "simpld.mm"
include "fssres2.mm"
include "sylancr.mm"
include "filtop.mm"
include "xpexg.mm"
include "mpdan.mm"
include "ssexd.mm"
include "fex.mm"
include "syl2anc.mm"
include "dirdm.mm"
include "syl.mm"
include "simpli.mm"
include "syl6reqr.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cfg.mm"
include "cima.mm"
include "c1st.mm"
include "wral.mm"
include "cpw.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "tailf.mm"
include "mpbird.mm"
include "adantr.mm"
include "ffn.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rexrn.mm"
include "3syl.mm"
include "wfun.mm"
include "wfo.mm"
include "fo2nd.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fnfun.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "ad2antrr.mm"
include "sseqtr4d.mm"
include "fndm.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "wbr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "vex.mm"
include "a1i.mm"
include "eltail.mm"
include "syl3anc.mm"
include "biantrurd.mm"
include "anbi1d.mm"
include "filnetlem1.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "imbi1d.mm"
include "fvres.mm"
include "eleq1d.mm"
include "pm5.74i.mm"
include "impexp.mm"
include "bitri.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "csn.mm"
include "ciun.mm"
include "cop.mm"
include "op1std.mm"
include "op2ndd.mm"
include "imbi12d.mm"
include "raliunxp.mm"
include "weq.mm"
include "sneq.mm"
include "id.mm"
include "xpeq12d.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "raleqi.mm"
include "dfss3.mm"
include "imbi2i.mm"
include "r19.21v.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "3bitr4i.mm"
include "rexbii.mm"
include "rexeqi.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "rexiunxp.mm"
include "3bitri.mm"
include "c0.mm"
include "wne.mm"
include "fileln0.mm"
include "adantlr.mm"
include "r19.9rzv.mm"
include "ssid.mm"
include "sseq1.mm"
include "rspcv.mm"
include "mpii.mm"
include "adantl.mm"
include "sstr2.mm"
include "com12.mm"
include "ralrimivw.mm"
include "impbid1.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "3bitrd.mm"
include "pm5.32da.mm"
include "cfbas.mm"
include "wn.mm"
include "filn0.mm"
include "wo.mm"
include "snnz.mm"
include "jctil.mm"
include "neanior.mm"
include "sylib.mm"
include "ss0b.mm"
include "xpeq0.mm"
include "sylnibr.mm"
include "ralrimiva.mm"
include "r19.2z.mm"
include "rexnal.mm"
include "sseq1i.mm"
include "iunss.mm"
include "3bitr3i.mm"
include "necon3abii.mm"
include "sylibr.mm"
include "cid.mm"
include "dmresi.mm"
include "filnetlem2.mm"
include "dmss.mm"
include "eqsstr3i.mm"
include "dmxpid.mm"
include "sseqtri.mm"
include "eqssi.mm"
include "tailfb.mm"
include "elfm.mm"
include "filfbas.mm"
include "elfg.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "fgfil.mm"
include "eqtr2d.mm"
include "jca.mm"
include "feq1.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "dmeq.mm"
include "fveq2.mm"
include "rneqd.mm"
include "fveq2d.mm"
include "exbidv.mm"
include "rspcev.mm"

theorem filnetlem4
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cX: class X
  let vd: setvar d
  let cA: class A
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  assume filnet.h: |- H = U_ n e. F ( { n } X. n )
  assume filnet.d: |- D = { <. x , y >. | ( ( x e. H /\ y e. H ) /\ ( 1st ` y ) C_ ( 1st ` x ) ) }

  disjoint x y
  disjoint d f
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint F d
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint H d
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint D d
  disjoint D f
  disjoint X d
  disjoint X f
  disjoint X n
  disjoint A x
  disjoint A y
  disjoint d k
  disjoint d m
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d z
  disjoint f k
  disjoint f m
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint H m
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H z
  disjoint B x
  disjoint B y
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( F e. ( Fil ` X ) -> E. d e. DirRel E. f ( f : dom d --> X /\ F = ( ( X FilMap f ) ` ran ( tail ` d ) ) ) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cD
    cdir
    wcel
    #
    cD
    cdm
    #
    cX
    vf
    cv
    #
    wf
    #
    cF
    cD
    ctail
    cfv
    #
    crn
    #
    cX
    @4
    cfm
    co
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vd
    cv
    #
    cdm
    #
    cX
    @4
    wf
    #
    cF
    @13
    ctail
    cfv
    #
    crn
    #
    @8
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vd
    cdir
    wrex
    @1
    cH
    cF
    cX
    cxp
    #
    wss
    #
    @2
    cH
    cD
    cuni
    cuni
    #
    wceq
    #
    @1
    @23
    @2
    wa
    wi
    #
    vx
    vy
    cD
    vn
    cF
    cH
    cX
    filnet.h
    filnet.d
    filnetlem3
    #
    simpri
    #
    simprd
    #
    @1
    c2nd
    cH
    cres
    #
    cvv
    wcel
    #
    @3
    cX
    @30
    wf
    #
    cF
    @7
    cX
    @30
    cfm
    co
    #
    cfv
    #
    wceq
    #
    wa
    #
    @12
    @1
    cH
    cX
    @30
    wf
    #
    cH
    cvv
    wcel
    @31
    @1
    @22
    cX
    c2nd
    @22
    cres
    wf
    @23
    @37
    cF
    cX
    f2ndres
    @1
    @23
    @2
    @28
    simpld
    #
    @22
    cX
    cH
    c2nd
    fssres2
    sylancr
    #
    @1
    cH
    @22
    cvv
    @1
    cX
    cF
    wcel
    #
    @22
    cvv
    wcel
    cF
    cX
    filtop
    #
    cF
    cX
    @0
    cF
    xpexg
    mpdan
    @38
    ssexd
    cH
    cX
    cvv
    @30
    fex
    syl2anc
    @1
    @32
    @35
    @1
    @37
    @32
    @39
    @1
    cH
    @3
    cX
    @30
    @1
    @3
    @24
    cH
    @1
    @2
    @3
    @24
    wceq
    @29
    cD
    dirdm
    syl
    @25
    @26
    @27
    simpli
    syl6reqr
    #
    feq2d
    mpbid
    @1
    @34
    cX
    cF
    cfg
    co
    #
    cF
    @1
    vt
    @34
    @43
    @1
    vt
    cv
    #
    cX
    wss
    #
    @30
    @13
    cima
    #
    @44
    wss
    #
    vd
    @7
    wrex
    #
    wa
    #
    @45
    vn
    cv
    #
    @44
    wss
    #
    vn
    cF
    wrex
    #
    wa
    #
    @44
    @34
    wcel
    #
    @44
    @43
    wcel
    #
    @1
    @45
    @48
    @52
    @1
    @45
    wa
    #
    @48
    @30
    @4
    @6
    cfv
    #
    cima
    #
    @44
    wss
    #
    vf
    cH
    wrex
    #
    @13
    c1st
    cfv
    #
    @4
    c1st
    cfv
    #
    wss
    #
    @13
    c2nd
    cfv
    #
    @44
    wcel
    #
    wi
    #
    vd
    cH
    wral
    #
    vf
    cH
    wrex
    #
    @52
    @56
    cH
    @3
    cpw
    #
    @6
    wf
    #
    @6
    cH
    wfn
    @48
    @60
    wb
    @1
    @70
    @45
    @1
    @70
    @3
    @69
    @6
    wf
    #
    @1
    @2
    @71
    @29
    cD
    @3
    @3
    eqid
    #
    tailf
    syl
    @1
    cH
    @3
    @69
    @6
    @42
    feq2d
    mpbird
    adantr
    #
    cH
    @69
    @6
    ffn
    @47
    @59
    vd
    vf
    cH
    @6
    @13
    @57
    wceq
    @46
    @58
    @44
    @13
    @57
    @30
    imaeq2
    sseq1d
    rexrn
    3syl
    @56
    @59
    @67
    vf
    cH
    @56
    @4
    cH
    wcel
    #
    wa
    #
    @59
    @13
    @30
    cfv
    #
    @44
    wcel
    #
    vd
    @57
    wral
    #
    @67
    @75
    @30
    wfun
    #
    @57
    @30
    cdm
    #
    wss
    @59
    @78
    wb
    @30
    cH
    wfn
    #
    @79
    c2nd
    cvv
    wfn
    #
    cH
    cvv
    wss
    @81
    cvv
    cvv
    c2nd
    wfo
    @82
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    cH
    ssv
    cvv
    cH
    c2nd
    fnssres
    mp2an
    #
    cH
    @30
    fnfun
    ax-mp
    @75
    @57
    cH
    @80
    @75
    @57
    @3
    cH
    @75
    @57
    @3
    @56
    cH
    @69
    @4
    @6
    @73
    ffvelrnda
    elpwid
    @1
    cH
    @3
    wceq
    @45
    @74
    @42
    ad2antrr
    #
    sseqtr4d
    @81
    @80
    cH
    wceq
    @83
    cH
    @30
    fndm
    ax-mp
    syl6sseqr
    vd
    @57
    @44
    @30
    funimass4
    sylancr
    @75
    @77
    @66
    vd
    @57
    cH
    @75
    @13
    @57
    wcel
    #
    @77
    wi
    @13
    cH
    wcel
    #
    @63
    wa
    #
    @77
    wi
    #
    @86
    @66
    wi
    #
    @75
    @85
    @87
    @77
    @75
    @85
    @4
    @13
    cD
    wbr
    #
    @87
    @75
    @2
    @4
    @3
    wcel
    @13
    cvv
    wcel
    #
    @85
    @90
    wb
    @1
    @2
    @45
    @74
    @29
    ad2antrr
    @75
    @4
    cH
    @3
    @56
    @74
    simpr
    #
    @84
    eleqtrd
    @91
    @75
    vd
    vex
    #
    a1i
    @4
    @13
    cvv
    cD
    @3
    @72
    eltail
    syl3anc
    @75
    @87
    @74
    @86
    wa
    #
    @63
    wa
    @90
    @75
    @86
    @94
    @63
    @75
    @74
    @86
    @92
    biantrurd
    anbi1d
    vx
    vy
    @4
    @13
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    vf
    vex
    @93
    filnetlem1
    syl6bbr
    bitr4d
    imbi1d
    @88
    @87
    @65
    wi
    @89
    @87
    @77
    @65
    @86
    @77
    @65
    wb
    @63
    @86
    @76
    @64
    @44
    @13
    cH
    c2nd
    fvres
    eleq1d
    adantr
    pm5.74i
    @86
    @63
    @65
    impexp
    bitri
    syl6bb
    ralbidv2
    bitrd
    rexbidva
    @68
    vk
    cv
    #
    @50
    wss
    #
    @95
    @44
    wss
    #
    wi
    #
    vk
    cF
    wral
    #
    vm
    @50
    wrex
    #
    vn
    cF
    wrex
    #
    @56
    @52
    @68
    @95
    @62
    wss
    #
    @97
    wi
    #
    vk
    cF
    wral
    #
    vf
    cH
    wrex
    @104
    vf
    vn
    cF
    @50
    csn
    #
    @50
    cxp
    #
    ciun
    #
    wrex
    @101
    @67
    @104
    vf
    cH
    @66
    vd
    vk
    cF
    @95
    csn
    #
    @95
    cxp
    #
    ciun
    #
    wral
    @102
    vv
    cv
    #
    @44
    wcel
    #
    wi
    #
    vv
    @95
    wral
    #
    vk
    cF
    wral
    @67
    @104
    @66
    @113
    vd
    vk
    vv
    cF
    @95
    @13
    @95
    @111
    cop
    wceq
    #
    @63
    @102
    @65
    @112
    @115
    @61
    @95
    @62
    @95
    @111
    @13
    vk
    vex
    #
    vv
    vex
    #
    op1std
    sseq1d
    @115
    @64
    @111
    @44
    @95
    @111
    @13
    @116
    @117
    op2ndd
    eleq1d
    imbi12d
    raliunxp
    @66
    vd
    cH
    @110
    cH
    @107
    @110
    filnet.h
    vn
    vk
    cF
    @106
    @109
    vn
    vk
    weq
    #
    @105
    @108
    @50
    @95
    @50
    @95
    sneq
    @118
    id
    xpeq12d
    cbviunv
    eqtri
    raleqi
    @103
    @114
    vk
    cF
    @103
    @102
    @112
    vv
    @95
    wral
    #
    wi
    @114
    @97
    @119
    @102
    vv
    @95
    @44
    dfss3
    imbi2i
    @102
    @112
    vv
    @95
    r19.21v
    bitr4i
    ralbii
    3bitr4i
    rexbii
    @104
    vf
    cH
    @107
    filnet.h
    rexeqi
    @104
    @99
    vf
    vn
    vm
    cF
    @50
    @4
    @50
    vm
    cv
    #
    cop
    wceq
    #
    @103
    @98
    vk
    cF
    @121
    @102
    @96
    @97
    @121
    @62
    @50
    @95
    @50
    @120
    @4
    vn
    vex
    #
    vm
    vex
    op1std
    sseq2d
    imbi1d
    ralbidv
    rexiunxp
    3bitri
    @56
    @100
    @51
    vn
    cF
    @56
    @50
    cF
    wcel
    #
    wa
    #
    @99
    @100
    @51
    @124
    @50
    c0
    wne
    #
    @99
    @100
    wb
    @1
    @123
    @125
    @45
    @50
    cF
    cX
    fileln0
    #
    adantlr
    @99
    vm
    @50
    r19.9rzv
    syl
    @124
    @99
    @51
    @123
    @99
    @51
    wi
    @56
    @123
    @99
    @50
    @50
    wss
    #
    @51
    @50
    ssid
    @98
    @127
    @51
    wi
    vk
    @50
    cF
    vk
    vn
    weq
    @96
    @127
    @97
    @51
    @95
    @50
    @50
    sseq1
    @95
    @50
    @44
    sseq1
    imbi12d
    rspcv
    mpii
    adantl
    @51
    @98
    vk
    cF
    @96
    @51
    @97
    @95
    @50
    @44
    sstr2
    com12
    ralrimivw
    impbid1
    bitr3d
    rexbidva
    syl5bb
    3bitrd
    pm5.32da
    @1
    @40
    @7
    cH
    cfbas
    cfv
    wcel
    #
    @37
    @54
    @49
    wb
    @41
    @1
    @2
    cH
    c0
    wne
    #
    @128
    @29
    @1
    @106
    c0
    wss
    #
    vn
    cF
    wral
    #
    wn
    #
    @129
    @1
    @130
    wn
    #
    vn
    cF
    wrex
    #
    @132
    @1
    cF
    c0
    wne
    @133
    vn
    cF
    wral
    @134
    cF
    cX
    filn0
    @1
    @133
    vn
    cF
    @1
    @123
    wa
    #
    @105
    c0
    wceq
    @50
    c0
    wceq
    wo
    #
    @130
    @135
    @105
    c0
    wne
    #
    @125
    wa
    @136
    wn
    @135
    @125
    @137
    @126
    @50
    @122
    snnz
    jctil
    @105
    c0
    @50
    c0
    neanior
    sylib
    @130
    @106
    c0
    wceq
    @136
    @106
    ss0b
    @105
    @50
    xpeq0
    bitri
    sylnibr
    ralrimiva
    @133
    vn
    cF
    r19.2z
    syl2anc
    @130
    vn
    cF
    rexnal
    sylib
    @131
    cH
    c0
    cH
    c0
    wss
    @107
    c0
    wss
    cH
    c0
    wceq
    @131
    cH
    @107
    c0
    filnet.h
    sseq1i
    cH
    ss0b
    vn
    cF
    @106
    c0
    iunss
    3bitr3i
    necon3abii
    sylibr
    cD
    cH
    cH
    @3
    cH
    cid
    cH
    cres
    #
    cdm
    #
    @3
    cH
    dmresi
    @138
    cD
    wss
    #
    @139
    @3
    wss
    @140
    cD
    cH
    cH
    cxp
    #
    wss
    #
    vx
    vy
    cD
    vn
    cF
    cH
    filnet.h
    filnet.d
    filnetlem2
    #
    simpli
    @138
    cD
    dmss
    ax-mp
    eqsstr3i
    @3
    @141
    cdm
    #
    cH
    @142
    @3
    @144
    wss
    @140
    @142
    @143
    simpri
    cD
    @141
    dmss
    ax-mp
    cH
    dmxpid
    sseqtri
    eqssi
    tailfb
    syl2anc
    @39
    vd
    @44
    @7
    cF
    @30
    cX
    cH
    elfm
    syl3anc
    @1
    cF
    cX
    cfbas
    cfv
    wcel
    @55
    @53
    wb
    cF
    cX
    filfbas
    vn
    @44
    cF
    cX
    elfg
    syl
    3bitr4d
    eqrdv
    cF
    cX
    fgfil
    eqtr2d
    jca
    @11
    @36
    vf
    @30
    cvv
    @4
    @30
    wceq
    #
    @5
    @32
    @10
    @35
    @3
    cX
    @4
    @30
    feq1
    @145
    @9
    @34
    cF
    @145
    @7
    @8
    @33
    @4
    @30
    cX
    cfm
    oveq2
    fveq1d
    eqeq2d
    anbi12d
    spcegv
    sylc
    @21
    @12
    vd
    cD
    cdir
    @13
    cD
    wceq
    #
    @20
    @11
    vf
    @146
    @15
    @5
    @19
    @10
    @146
    @14
    @3
    cX
    @4
    @13
    cD
    dmeq
    feq2d
    @146
    @18
    @9
    cF
    @146
    @17
    @7
    @8
    @146
    @16
    @6
    @13
    cD
    ctail
    fveq2
    rneqd
    fveq2d
    eqeq2d
    anbi12d
    exbidv
    rspcev
    syl2anc
end
