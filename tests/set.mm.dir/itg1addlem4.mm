include "caddc.mm"
include "cof.mm"
include "co.mm"
include "citg1.mm"
include "cfv.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "cmul.mm"
include "csu.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfn.mm"
include "wss.mm"
include "cr.mm"
include "wceq.mm"
include "i1fadd.mm"
include "cxp.mm"
include "wfo.mm"
include "i1frn.mm"
include "syl.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "wfn.mm"
include "cres.mm"
include "cc.mm"
include "wf.mm"
include "ax-addf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "i1ff.mm"
include "frn.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "xpss12.mm"
include "fnssres.mm"
include "sylancr.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "difss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cvv.mm"
include "wa.mm"
include "cop.mm"
include "opelxpi.mm"
include "wfun.mm"
include "wi.mm"
include "ffun.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "funfvima2.mm"
include "syl5.mm"
include "imp.mm"
include "df-ov.mm"
include "rneqi.mm"
include "df-ima.mm"
include "eqtr4i.mm"
include "3eltr4g.mm"
include "dffn3.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "ssdifd.mm"
include "wral.mm"
include "sselda.mm"
include "anim12dan.mm"
include "readdcl.mm"
include "ralrimivva.mm"
include "wb.mm"
include "funimassov.mm"
include "mpbird.mm"
include "syl5eqss.mm"
include "itg1val2.mm"
include "syl13anc.mm"
include "cin.mm"
include "ciun.mm"
include "adantr.mm"
include "inss2.mm"
include "i1fima.mm"
include "inmbl.mm"
include "ad2antrr.mm"
include "wn.mm"
include "syl5ss.mm"
include "adantlr.mm"
include "resubcld.mm"
include "wne.mm"
include "recnd.mm"
include "npcand.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "eqnetrd.mm"
include "oveq12.mm"
include "00id.mm"
include "syl6eq.mm"
include "necon3ai.mm"
include "itg1addlem3.mm"
include "syl21anc.mm"
include "itg1addlem2.mm"
include "fovrnd.mm"
include "eqeltrrd.mm"
include "itg1addlem1.mm"
include "i1faddlem.mm"
include "syldan.mm"
include "fveq2d.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "fsummulc2.mm"
include "eqtrd.mm"
include "mulcld.mm"
include "anasss.mm"
include "fsumcom.mm"
include "3eqtrd.mm"
include "cmpt.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "wf1.mm"
include "wf1o.mm"
include "ex.mm"
include "adantrr.mm"
include "ad2ant2rl.mm"
include "subcan2ad.mm"
include "dom2lem.mm"
include "f1f1orn.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "f1f.mm"
include "3syl.mm"
include "readdcld.mm"
include "remulcld.mm"
include "fsumf1o.mm"
include "oveq1d.mm"
include "wrex.mm"
include "cab.mm"
include "simpr.mm"
include "simplr.mm"
include "mpan.mm"
include "sylc.mm"
include "pncand.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "ssabral.mm"
include "rnmpt.mm"
include "eldifi.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "c0.mm"
include "inss1.mm"
include "eldifn.mm"
include "wbr.mm"
include "vex.mm"
include "eliniseg.mm"
include "brelrn.mm"
include "sylbi.mm"
include "nsyl.mm"
include "pm2.21d.mm"
include "ssrdv.mm"
include "ss0.mm"
include "covol.mm"
include "0mbl.mm"
include "mblvol.mm"
include "ovol0.mm"
include "eqtri.mm"
include "mul01d.mm"
include "expr.mm"
include "0re.mm"
include "cif.mm"
include "iftrue.mm"
include "c0ex.mm"
include "ovmpt2a.mm"
include "mp2an.mm"
include "0cn.mm"
include "mul01i.mm"
include "pm2.61d2.mm"
include "f1ofo.mm"
include "fsumss.mm"
include "an32s.mm"
include "dfin4.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "elsni.mm"
include "syl6eqel.mm"
include "mul02d.mm"
include "sylan2.mm"
include "3eqtr2d.mm"

theorem itg1addlem4
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cI: class I
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vv: setvar v
  let vx: setvar x
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )
  assume itg1add.3: |- I = ( i e. RR , j e. RR |-> if ( ( i = 0 /\ j = 0 ) , 0 , ( vol ` ( ( `' F " { i } ) i^i ( `' G " { j } ) ) ) ) )
  assume itg1add.4: |- P = ( + |` ( ran F X. ran G ) )

  disjoint i j
  disjoint i y
  disjoint i z
  disjoint j y
  disjoint j z
  disjoint y z
  disjoint I y
  disjoint P y
  disjoint P z
  disjoint F i
  disjoint F j
  disjoint F y
  disjoint F z
  disjoint G i
  disjoint G j
  disjoint G y
  disjoint G z
  disjoint i ph
  disjoint j ph
  disjoint ph y
  disjoint ph z
  disjoint A i
  disjoint A j
  disjoint A y
  disjoint A z
  disjoint B i
  disjoint B j
  disjoint w y
  disjoint I w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint x y
  disjoint x z
  disjoint P x
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint ph v
  disjoint ph w
  disjoint ph x
  assert |- ( ph -> ( S.1 ` ( F oF + G ) ) = sum_ y e. ran F sum_ z e. ran G ( ( y + z ) x. ( y I z ) ) )

  proof
    wph
    cF
    cG
    caddc
    cof
    co
    #
    citg1
    cfv
    #
    cG
    crn
    #
    cP
    crn
    #
    cc0
    csn
    #
    cdif
    #
    vw
    cv
    #
    @6
    vz
    cv
    #
    cmin
    co
    #
    @7
    cI
    co
    #
    cmul
    co
    #
    vw
    csu
    #
    vz
    csu
    #
    @2
    cF
    crn
    #
    vy
    cv
    #
    @7
    caddc
    co
    #
    @14
    @7
    cI
    co
    #
    cmul
    co
    #
    vy
    csu
    #
    vz
    csu
    @13
    @2
    @17
    vz
    csu
    vy
    csu
    wph
    @1
    @5
    @6
    @0
    ccnv
    @6
    csn
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vw
    csu
    #
    @5
    @2
    @10
    vz
    csu
    #
    vw
    csu
    @12
    wph
    @0
    citg1
    cdm
    #
    wcel
    @5
    cfn
    wcel
    #
    @0
    crn
    #
    @4
    cdif
    @5
    wss
    @5
    cr
    @4
    cdif
    wss
    @1
    @22
    wceq
    wph
    cF
    cG
    i1fadd.1
    i1fadd.2
    i1fadd
    wph
    @3
    cfn
    wcel
    #
    @5
    @3
    wss
    #
    @25
    wph
    @13
    @2
    cxp
    #
    cfn
    wcel
    #
    @29
    @3
    cP
    wfo
    #
    @27
    wph
    @13
    cfn
    wcel
    #
    @2
    cfn
    wcel
    #
    @30
    wph
    cF
    @24
    wcel
    #
    @32
    i1fadd.1
    cF
    i1frn
    syl
    #
    wph
    cG
    @24
    wcel
    #
    @33
    i1fadd.2
    cG
    i1frn
    syl
    #
    @13
    @2
    xpfi
    syl2anc
    wph
    cP
    @29
    wfn
    #
    @31
    wph
    caddc
    @29
    cres
    #
    @29
    wfn
    #
    @38
    wph
    caddc
    cc
    cc
    cxp
    #
    wfn
    #
    @29
    @41
    wss
    #
    @40
    @41
    cc
    caddc
    wf
    #
    @42
    ax-addf
    @41
    cc
    caddc
    ffn
    ax-mp
    wph
    @13
    cc
    wss
    @2
    cc
    wss
    @43
    wph
    @13
    cr
    cc
    wph
    cr
    cr
    cF
    wf
    #
    @13
    cr
    wss
    wph
    @34
    @45
    i1fadd.1
    cF
    i1ff
    syl
    #
    cr
    cr
    cF
    frn
    syl
    #
    ax-resscn
    syl6ss
    wph
    @2
    cr
    cc
    wph
    cr
    cr
    cG
    wf
    #
    @2
    cr
    wss
    wph
    @36
    @48
    i1fadd.2
    cG
    i1ff
    syl
    #
    cr
    cr
    cG
    frn
    syl
    #
    ax-resscn
    syl6ss
    @13
    cc
    @2
    cc
    xpss12
    syl2anc
    #
    @41
    @29
    caddc
    fnssres
    sylancr
    @29
    cP
    @39
    itg1add.4
    fneq1i
    sylibr
    @29
    cP
    dffn4
    sylib
    @29
    @3
    cP
    fofi
    syl2anc
    #
    @3
    @4
    difss
    #
    @3
    @5
    ssfi
    sylancl
    #
    wph
    @26
    @3
    @4
    wph
    cr
    @3
    @0
    wf
    @26
    @3
    wss
    wph
    vx
    vy
    cr
    cr
    cr
    caddc
    @13
    @2
    @3
    cF
    cG
    cvv
    cvv
    wph
    vx
    cv
    #
    @13
    wcel
    @14
    @2
    wcel
    wa
    #
    wa
    @55
    @14
    cop
    #
    caddc
    cfv
    #
    caddc
    @29
    cima
    #
    @55
    @14
    caddc
    co
    @3
    wph
    @56
    @58
    @59
    wcel
    #
    @56
    @57
    @29
    wcel
    #
    wph
    @60
    @55
    @14
    @13
    @2
    opelxpi
    wph
    caddc
    wfun
    #
    @29
    caddc
    cdm
    #
    wss
    #
    @61
    @60
    wi
    @44
    @62
    ax-addf
    @41
    cc
    caddc
    ffun
    ax-mp
    #
    wph
    @29
    @41
    @63
    @51
    @41
    cc
    caddc
    ax-addf
    fdmi
    syl6sseqr
    #
    @29
    @57
    caddc
    funfvima2
    sylancr
    syl5
    imp
    @55
    @14
    caddc
    df-ov
    @3
    @39
    crn
    @59
    cP
    @39
    itg1add.4
    rneqi
    caddc
    @29
    df-ima
    eqtr4i
    #
    3eltr4g
    wph
    cF
    cr
    wfn
    #
    cr
    @13
    cF
    wf
    wph
    @45
    @68
    @46
    cr
    cr
    cF
    ffn
    syl
    cr
    cF
    dffn3
    sylib
    wph
    cG
    cr
    wfn
    #
    cr
    @2
    cG
    wf
    wph
    @48
    @69
    @49
    cr
    cr
    cG
    ffn
    syl
    cr
    cG
    dffn3
    sylib
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    @70
    cr
    inidm
    off
    cr
    @3
    @0
    frn
    syl
    ssdifd
    wph
    @3
    cr
    @4
    wph
    @3
    @59
    cr
    @67
    wph
    @59
    cr
    wss
    #
    @15
    cr
    wcel
    #
    vz
    @2
    wral
    vy
    @13
    wral
    #
    wph
    @72
    vy
    vz
    @13
    @2
    wph
    @14
    @13
    wcel
    #
    @7
    @2
    wcel
    #
    wa
    wa
    @14
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    wa
    @72
    wph
    @74
    @76
    @75
    @77
    wph
    @13
    cr
    @14
    @47
    sselda
    #
    wph
    @2
    cr
    @7
    @50
    sselda
    #
    anim12dan
    @14
    @7
    readdcl
    syl
    ralrimivva
    wph
    @62
    @64
    @71
    @73
    wb
    @65
    @66
    vy
    vz
    @13
    @2
    cr
    caddc
    funimassov
    sylancr
    mpbird
    syl5eqss
    #
    ssdifd
    vw
    @5
    @0
    itg1val2
    syl13anc
    wph
    @5
    @21
    @23
    vw
    wph
    @6
    @5
    wcel
    #
    wa
    #
    @21
    @6
    @2
    @9
    vz
    csu
    #
    cmul
    co
    @23
    @82
    @20
    @83
    @6
    cmul
    @82
    vz
    @2
    cF
    ccnv
    #
    @8
    csn
    #
    cima
    #
    cG
    ccnv
    #
    @7
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    cvol
    cfv
    @2
    @90
    cvol
    cfv
    #
    vz
    csu
    @20
    @83
    @82
    @2
    @90
    vz
    cG
    cr
    cr
    wph
    @48
    @81
    @49
    adantr
    wph
    @33
    @81
    @37
    adantr
    #
    @90
    @89
    wss
    @82
    @75
    wa
    #
    @86
    @89
    inss2
    a1i
    wph
    @90
    cvol
    cdm
    #
    wcel
    #
    @81
    @75
    wph
    @86
    @95
    wcel
    #
    @89
    @95
    wcel
    #
    @96
    wph
    @34
    @97
    i1fadd.1
    @85
    cF
    i1fima
    syl
    wph
    @36
    @98
    i1fadd.2
    @88
    cG
    i1fima
    syl
    @86
    @89
    inmbl
    syl2anc
    ad2antrr
    @94
    @9
    @92
    cr
    @94
    @8
    cr
    wcel
    @77
    @8
    cc0
    wceq
    @7
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @9
    @92
    wceq
    @94
    @6
    @7
    @82
    @6
    cr
    wcel
    @75
    wph
    @5
    cr
    @6
    wph
    @5
    @3
    cr
    @53
    @80
    syl5ss
    sselda
    #
    adantr
    #
    wph
    @75
    @77
    @81
    @79
    adantlr
    #
    resubcld
    #
    @104
    @94
    @8
    @7
    caddc
    co
    #
    cc0
    wne
    @101
    @94
    @106
    @6
    cc0
    @94
    @6
    @7
    @94
    @6
    @103
    recnd
    #
    @94
    @7
    @104
    recnd
    npcand
    @81
    @6
    cc0
    wne
    wph
    @75
    @6
    @3
    cc0
    eldifsni
    ad2antlr
    eqnetrd
    @100
    @106
    cc0
    @100
    @106
    cc0
    cc0
    caddc
    co
    #
    cc0
    @8
    cc0
    @7
    cc0
    caddc
    oveq12
    00id
    syl6eq
    necon3ai
    syl
    wph
    @8
    @7
    vi
    vj
    cF
    cG
    cI
    i1fadd.1
    i1fadd.2
    itg1add.3
    itg1addlem3
    syl21anc
    #
    @94
    @8
    @7
    cr
    cr
    cr
    cI
    wph
    cr
    cr
    cxp
    cr
    cI
    wf
    #
    @81
    @75
    wph
    vi
    vj
    cF
    cG
    cI
    i1fadd.1
    i1fadd.2
    itg1add.3
    itg1addlem2
    #
    ad2antrr
    @105
    @104
    fovrnd
    #
    eqeltrrd
    itg1addlem1
    @82
    @19
    @91
    cvol
    wph
    @81
    @6
    cc
    wcel
    @19
    @91
    wceq
    @82
    @6
    @102
    recnd
    #
    wph
    vz
    @6
    cF
    cG
    i1fadd.1
    i1fadd.2
    i1faddlem
    syldan
    fveq2d
    @82
    @2
    @9
    @92
    vz
    @109
    sumeq2dv
    3eqtr4d
    oveq2d
    @82
    @2
    @9
    @6
    vz
    @93
    @113
    @94
    @9
    @112
    recnd
    #
    fsummulc2
    eqtrd
    sumeq2dv
    wph
    @5
    @2
    @10
    vw
    vz
    @54
    @37
    wph
    @81
    @75
    @10
    cc
    wcel
    #
    @94
    @6
    @9
    @107
    @114
    mulcld
    #
    anasss
    fsumcom
    3eqtrd
    wph
    @2
    @18
    @11
    vz
    wph
    @75
    wa
    #
    vv
    @3
    vv
    cv
    #
    @7
    cmin
    co
    #
    cmpt
    #
    crn
    #
    @17
    vy
    csu
    #
    @3
    @10
    vw
    csu
    #
    @18
    @11
    @117
    @122
    @3
    @106
    @9
    cmul
    co
    #
    vw
    csu
    @123
    @117
    @121
    @17
    @3
    @124
    vy
    vw
    @120
    @8
    @14
    @8
    wceq
    @15
    @106
    @16
    @9
    cmul
    @14
    @8
    @7
    caddc
    oveq1
    @14
    @8
    @7
    cI
    oveq1
    oveq12d
    wph
    @27
    @75
    @52
    adantr
    #
    @117
    @3
    cr
    @120
    wf1
    #
    @3
    @121
    @120
    wf1o
    #
    @117
    vv
    vy
    @3
    cr
    @119
    @14
    @7
    cmin
    co
    #
    @117
    @118
    @3
    wcel
    #
    @119
    cr
    wcel
    @117
    @129
    wa
    #
    @118
    @7
    @117
    @3
    cr
    @118
    wph
    @3
    cr
    wss
    @75
    @80
    adantr
    #
    sselda
    #
    @117
    @77
    @129
    @79
    adantr
    resubcld
    ex
    @117
    @129
    @14
    @3
    wcel
    #
    wa
    #
    @119
    @128
    wceq
    @118
    @14
    wceq
    wb
    @117
    @134
    wa
    #
    @118
    @14
    @7
    @117
    @129
    @118
    cc
    wcel
    @133
    @130
    @118
    @132
    recnd
    adantrr
    @135
    @14
    wph
    @133
    @76
    @75
    @129
    wph
    @3
    cr
    @14
    @80
    sselda
    ad2ant2rl
    recnd
    @117
    @7
    cc
    wcel
    #
    @134
    @117
    @7
    @79
    recnd
    #
    adantr
    subcan2ad
    ex
    dom2lem
    #
    @3
    cr
    @120
    f1f1orn
    syl
    #
    @6
    @3
    wcel
    #
    @6
    @120
    cfv
    @8
    wceq
    @117
    vv
    @6
    @119
    @8
    @3
    @120
    @118
    @6
    @7
    cmin
    oveq1
    @120
    eqid
    #
    @6
    @7
    cmin
    ovex
    fvmpt
    adantl
    @117
    @14
    @121
    wcel
    #
    wa
    #
    @17
    @143
    @15
    @16
    @143
    @14
    @7
    @117
    @121
    cr
    @14
    @117
    @126
    @3
    cr
    @120
    wf
    @121
    cr
    wss
    @138
    @3
    cr
    @120
    f1f
    @3
    cr
    @120
    frn
    3syl
    #
    sselda
    #
    @117
    @77
    @142
    @79
    adantr
    #
    readdcld
    @143
    @14
    @7
    cr
    cr
    cr
    cI
    wph
    @110
    @75
    @142
    @111
    ad2antrr
    @145
    @146
    fovrnd
    remulcld
    recnd
    fsumf1o
    @117
    @3
    @124
    @10
    vw
    @117
    @140
    wa
    #
    @106
    @6
    @9
    cmul
    @147
    @6
    @7
    @147
    @6
    @117
    @3
    cr
    @6
    @131
    sselda
    recnd
    @117
    @136
    @140
    @137
    adantr
    npcand
    oveq1d
    sumeq2dv
    eqtrd
    @117
    @13
    @121
    @17
    vy
    @117
    @13
    @14
    @119
    wceq
    #
    vv
    @3
    wrex
    #
    vy
    cab
    #
    @121
    @117
    @149
    vy
    @13
    wral
    @13
    @150
    wss
    @117
    @149
    vy
    @13
    @117
    @74
    wa
    #
    @15
    @3
    wcel
    @14
    @15
    @7
    cmin
    co
    #
    wceq
    #
    @149
    @151
    @14
    @7
    cop
    #
    caddc
    cfv
    #
    @59
    @15
    @3
    @151
    @64
    @154
    @29
    wcel
    #
    @155
    @59
    wcel
    #
    wph
    @64
    @75
    @74
    @66
    ad2antrr
    @151
    @74
    @75
    @156
    @117
    @74
    simpr
    wph
    @75
    @74
    simplr
    @14
    @7
    @13
    @2
    opelxpi
    syl2anc
    @62
    @64
    @156
    @157
    wi
    @65
    @29
    @154
    caddc
    funfvima2
    mpan
    sylc
    @14
    @7
    caddc
    df-ov
    @67
    3eltr4g
    @151
    @152
    @14
    @151
    @14
    @7
    @151
    @14
    wph
    @74
    @76
    @75
    @78
    adantlr
    #
    recnd
    @117
    @136
    @74
    @137
    adantr
    pncand
    eqcomd
    @148
    @153
    vv
    @15
    @3
    @118
    @15
    wceq
    @119
    @152
    @14
    @118
    @15
    @7
    cmin
    oveq1
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    @149
    vy
    @13
    ssabral
    sylibr
    vv
    vy
    @3
    @119
    @120
    @141
    rnmpt
    syl6sseqr
    @151
    @17
    @151
    @15
    @16
    @151
    @14
    @7
    @158
    @117
    @77
    @74
    @79
    adantr
    #
    readdcld
    @151
    @14
    @7
    cr
    cr
    cr
    cI
    wph
    @110
    @75
    @74
    @111
    ad2antrr
    @158
    @159
    fovrnd
    remulcld
    recnd
    #
    @117
    @14
    @121
    @13
    cdif
    #
    wcel
    @14
    cr
    @13
    cdif
    #
    wcel
    #
    @17
    cc0
    wceq
    #
    @117
    @161
    @162
    @14
    @117
    @121
    cr
    @13
    @144
    ssdifd
    sselda
    @117
    @163
    wa
    @14
    cc0
    wceq
    @99
    wa
    #
    @164
    @117
    @163
    @165
    wn
    #
    @164
    @117
    @163
    @166
    wa
    #
    wa
    #
    @17
    @15
    cc0
    cmul
    co
    cc0
    @168
    @16
    cc0
    @15
    cmul
    @168
    @16
    @84
    @14
    csn
    cima
    #
    @89
    cin
    #
    cvol
    cfv
    #
    cc0
    @168
    @76
    @77
    @166
    @16
    @171
    wceq
    @163
    @76
    @117
    @166
    @14
    cr
    @13
    eldifi
    ad2antrl
    #
    @117
    @77
    @167
    @79
    adantr
    #
    @117
    @163
    @166
    simprr
    wph
    @14
    @7
    vi
    vj
    cF
    cG
    cI
    i1fadd.1
    i1fadd.2
    itg1add.3
    itg1addlem3
    syl21anc
    @168
    @171
    c0
    cvol
    cfv
    #
    cc0
    @168
    @170
    c0
    cvol
    @168
    @170
    c0
    wss
    @170
    c0
    wceq
    @168
    @170
    @169
    c0
    @169
    @89
    inss1
    @168
    vv
    @169
    c0
    @168
    @118
    @169
    wcel
    #
    @118
    c0
    wcel
    @168
    @74
    @175
    @163
    @74
    wn
    @117
    @166
    @14
    cr
    @13
    eldifn
    ad2antrl
    @175
    @118
    @14
    cF
    wbr
    #
    @74
    @14
    cvv
    wcel
    @175
    @176
    wb
    vy
    vex
    #
    cF
    @14
    @118
    cvv
    vv
    vex
    #
    eliniseg
    ax-mp
    @118
    @14
    cF
    @178
    @177
    brelrn
    sylbi
    nsyl
    pm2.21d
    ssrdv
    syl5ss
    @170
    ss0
    syl
    fveq2d
    @174
    c0
    covol
    cfv
    #
    cc0
    c0
    @95
    wcel
    @174
    @179
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
    syl6eq
    eqtrd
    oveq2d
    @168
    @15
    @168
    @15
    @168
    @14
    @7
    @172
    @173
    readdcld
    recnd
    mul01d
    eqtrd
    expr
    @165
    @17
    cc0
    cc0
    cmul
    co
    cc0
    @165
    @15
    cc0
    @16
    cc0
    cmul
    @165
    @15
    @108
    cc0
    @14
    cc0
    @7
    cc0
    caddc
    oveq12
    00id
    syl6eq
    @165
    @16
    cc0
    cc0
    cI
    co
    #
    cc0
    @14
    cc0
    @7
    cc0
    cI
    oveq12
    cc0
    cr
    wcel
    #
    @181
    @180
    cc0
    wceq
    0re
    0re
    vi
    vj
    cc0
    cc0
    cr
    cr
    vi
    cv
    #
    cc0
    wceq
    vj
    cv
    #
    cc0
    wceq
    wa
    #
    cc0
    @84
    @182
    csn
    cima
    @87
    @183
    csn
    cima
    cin
    cvol
    cfv
    #
    cif
    cc0
    cI
    @184
    cc0
    @185
    iftrue
    itg1add.3
    c0ex
    ovmpt2a
    mp2an
    syl6eq
    oveq12d
    cc0
    0cn
    mul01i
    syl6eq
    pm2.61d2
    syldan
    @117
    @27
    @3
    @121
    @120
    wfo
    #
    @121
    cfn
    wcel
    @125
    @117
    @127
    @186
    @139
    @3
    @121
    @120
    f1ofo
    syl
    @3
    @121
    @120
    fofi
    syl2anc
    fsumss
    @117
    @5
    @3
    @10
    vw
    @28
    @117
    @53
    a1i
    wph
    @81
    @75
    @115
    @116
    an32s
    @6
    @3
    @5
    cdif
    #
    wcel
    @117
    @6
    @4
    wcel
    #
    @10
    cc0
    wceq
    @187
    @4
    @6
    @187
    @3
    @4
    cin
    @4
    @3
    @4
    dfin4
    @3
    @4
    inss2
    eqsstr3i
    sseli
    @117
    @188
    wa
    #
    @10
    cc0
    @9
    cmul
    co
    cc0
    @189
    @6
    cc0
    @9
    cmul
    @188
    @6
    cc0
    wceq
    @117
    @6
    cc0
    elsni
    adantl
    #
    oveq1d
    @189
    @9
    @189
    @9
    @189
    @8
    @7
    cr
    cr
    cr
    cI
    wph
    @110
    @75
    @188
    @111
    ad2antrr
    @189
    @6
    @7
    @189
    @6
    cc0
    cr
    @190
    0re
    syl6eqel
    @117
    @77
    @188
    @79
    adantr
    #
    resubcld
    @191
    fovrnd
    recnd
    mul02d
    eqtrd
    sylan2
    @125
    fsumss
    3eqtr4d
    sumeq2dv
    wph
    @2
    @13
    @17
    vz
    vy
    @37
    @35
    wph
    @75
    @74
    @17
    cc
    wcel
    @160
    anasss
    fsumcom
    3eqtr2d
end
