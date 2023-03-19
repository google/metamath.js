include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cphi.mm"
include "cxp.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cgcd.mm"
include "c1.mm"
include "cc0.mm"
include "cfzo.mm"
include "crab.mm"
include "wss.mm"
include "fzofi.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "hashxp.mm"
include "cen.mm"
include "wbr.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "cmo.mm"
include "cop.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "simplbi.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "syl.mm"
include "adantl.mm"
include "cz.mm"
include "cn.mm"
include "syl6eleq.mm"
include "elfzoelz.mm"
include "simp1d.mm"
include "adantr.mm"
include "zmodfzo.mm"
include "syl2anc.mm"
include "modgcd.mm"
include "cle.mm"
include "cdvds.mm"
include "nnzd.mm"
include "gcddvds.mm"
include "simpld.mm"
include "simprd.mm"
include "simp2d.mm"
include "dvdsmul1.mm"
include "wi.mm"
include "wn.mm"
include "wne.mm"
include "nnne0.mm"
include "simpr.mm"
include "necon3ai.mm"
include "3syl.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnmulcld.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "dvdslegcd.mm"
include "syl31anc.mm"
include "simprbi.mm"
include "breqtrd.mm"
include "wb.mm"
include "nnle1eq1.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "sylanbrc.mm"
include "dvdsmul2.mm"
include "opelxpi.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wfun.mm"
include "cdm.mm"
include "wf1o.mm"
include "wfn.mm"
include "crth.mm"
include "f1ofn.mm"
include "fnfun.mm"
include "eqsstri.mm"
include "fndm.mm"
include "syl5sseqr.mm"
include "funimass4.mm"
include "mpbird.mm"
include "ccnv.mm"
include "xpss12.mm"
include "sseqtr4i.mm"
include "sseli.mm"
include "f1ocnvfv2.mm"
include "syl2an.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "eqtr3d.mm"
include "eqeltrrd.mm"
include "opelxp.mm"
include "sylib.mm"
include "rpmul.mm"
include "funfvima2.mm"
include "imp.mm"
include "syldan.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "wf1.mm"
include "f1of1.mm"
include "elexi.mm"
include "f1imaen.mm"
include "sylancl.mm"
include "eqbrtrrd.mm"
include "xpfi.mm"
include "hashen.mm"
include "sylibr.mm"
include "syl5reqr.mm"
include "dfphi2.mm"
include "rabeq.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem phimullem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vz: setvar z
  assume crth.1: |- S = ( 0 ..^ ( M x. N ) )
  assume crth.2: |- T = ( ( 0 ..^ M ) X. ( 0 ..^ N ) )
  assume crth.3: |- F = ( x e. S |-> <. ( x mod M ) , ( x mod N ) >. )
  assume crth.4: |- ( ph -> ( M e. NN /\ N e. NN /\ ( M gcd N ) = 1 ) )
  assume phimul.4: |- U = { y e. ( 0 ..^ M ) | ( y gcd M ) = 1 }
  assume phimul.5: |- V = { y e. ( 0 ..^ N ) | ( y gcd N ) = 1 }
  assume phimul.6: |- W = { y e. S | ( y gcd ( M x. N ) ) = 1 }

  disjoint F y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint N x
  disjoint N y
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F z
  disjoint w x
  disjoint M w
  disjoint ph w
  disjoint x z
  disjoint ph z
  disjoint S w
  disjoint S z
  disjoint N w
  disjoint U w
  disjoint U z
  disjoint V w
  disjoint V z
  disjoint W w
  disjoint W z
  assert |- ( ph -> ( phi ` ( M x. N ) ) = ( ( phi ` M ) x. ( phi ` N ) ) )

  proof
    wph
    cW
    chash
    cfv
    #
    cU
    chash
    cfv
    #
    cV
    chash
    cfv
    #
    cmul
    co
    #
    cM
    cN
    cmul
    co
    #
    cphi
    cfv
    #
    cM
    cphi
    cfv
    #
    cN
    cphi
    cfv
    #
    cmul
    co
    wph
    @3
    cU
    cV
    cxp
    #
    chash
    cfv
    #
    @0
    cU
    cfn
    wcel
    #
    cV
    cfn
    wcel
    #
    @9
    @3
    wceq
    cU
    vy
    cv
    #
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    vy
    cc0
    cM
    cfzo
    co
    #
    crab
    #
    cfn
    phimul.4
    @15
    cfn
    wcel
    @16
    @15
    wss
    @16
    cfn
    wcel
    cc0
    cM
    fzofi
    @14
    vy
    @15
    ssrab2
    #
    @15
    @16
    ssfi
    mp2an
    eqeltri
    #
    cV
    @12
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vy
    cc0
    cN
    cfzo
    co
    #
    crab
    #
    cfn
    phimul.5
    @21
    cfn
    wcel
    @22
    @21
    wss
    @22
    cfn
    wcel
    cc0
    cN
    fzofi
    @20
    vy
    @21
    ssrab2
    #
    @21
    @22
    ssfi
    mp2an
    eqeltri
    #
    cU
    cV
    hashxp
    mp2an
    wph
    @8
    cW
    cen
    wbr
    #
    @9
    @0
    wceq
    #
    wph
    cF
    cW
    cima
    #
    @8
    cW
    cen
    wph
    @27
    @8
    wph
    @27
    @8
    wss
    #
    vw
    cv
    #
    cF
    cfv
    #
    @8
    wcel
    #
    vw
    cW
    wral
    #
    wph
    @31
    vw
    cW
    wph
    @29
    cW
    wcel
    #
    wa
    #
    @30
    @29
    cM
    cmo
    co
    #
    @29
    cN
    cmo
    co
    #
    cop
    #
    @8
    @33
    @30
    @37
    wceq
    #
    wph
    @33
    @29
    cS
    wcel
    #
    @38
    @33
    @39
    @29
    @4
    cgcd
    co
    #
    c1
    wceq
    #
    @12
    @4
    cgcd
    co
    #
    c1
    wceq
    #
    @41
    vy
    @29
    cS
    cW
    @12
    @29
    wceq
    @42
    @40
    c1
    @12
    @29
    @4
    cgcd
    oveq1
    eqeq1d
    phimul.6
    elrab2
    #
    simplbi
    #
    vx
    @29
    vx
    cv
    #
    cM
    cmo
    co
    #
    @46
    cN
    cmo
    co
    #
    cop
    #
    @37
    cS
    cF
    @46
    @29
    wceq
    @47
    @35
    @48
    @36
    @46
    @29
    cM
    cmo
    oveq1
    @46
    @29
    cN
    cmo
    oveq1
    opeq12d
    #
    crth.3
    @35
    @36
    opex
    fvmpt
    syl
    adantl
    @34
    @35
    cU
    wcel
    #
    @36
    cV
    wcel
    #
    @37
    @8
    wcel
    @34
    @35
    @15
    wcel
    #
    @35
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    @51
    @34
    @29
    cz
    wcel
    #
    cM
    cn
    wcel
    #
    @53
    @34
    @29
    cc0
    @4
    cfzo
    co
    #
    wcel
    #
    @56
    @33
    @59
    wph
    @33
    @29
    cS
    @58
    @45
    crth.1
    syl6eleq
    adantl
    @29
    cc0
    @4
    elfzoelz
    syl
    #
    wph
    @57
    @33
    wph
    @57
    cN
    cn
    wcel
    #
    cM
    cN
    cgcd
    co
    c1
    wceq
    #
    crth.4
    simp1d
    #
    adantr
    #
    @29
    cM
    zmodfzo
    syl2anc
    @34
    @54
    @29
    cM
    cgcd
    co
    #
    c1
    @34
    @56
    @57
    @54
    @65
    wceq
    @60
    @64
    @29
    cM
    modgcd
    syl2anc
    @34
    @65
    c1
    cle
    wbr
    #
    @65
    c1
    wceq
    #
    @34
    @65
    @40
    c1
    cle
    @34
    @65
    @29
    cdvds
    wbr
    #
    @65
    @4
    cdvds
    wbr
    #
    @65
    @40
    cle
    wbr
    #
    @34
    @68
    @65
    cM
    cdvds
    wbr
    #
    @34
    @56
    cM
    cz
    wcel
    #
    @68
    @71
    wa
    @60
    @34
    cM
    @64
    nnzd
    #
    @29
    cM
    gcddvds
    syl2anc
    #
    simpld
    @34
    @71
    cM
    @4
    cdvds
    wbr
    #
    @69
    @34
    @68
    @71
    @74
    simprd
    @34
    @72
    cN
    cz
    wcel
    #
    @75
    @73
    @34
    cN
    wph
    @61
    @33
    wph
    @57
    @61
    @62
    crth.4
    simp2d
    #
    adantr
    #
    nnzd
    #
    cM
    cN
    dvdsmul1
    syl2anc
    @34
    @65
    cz
    wcel
    #
    @72
    @4
    cz
    wcel
    #
    @71
    @75
    wa
    @69
    wi
    @34
    @65
    @34
    @56
    @72
    @29
    cc0
    wceq
    #
    cM
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @65
    cn
    wcel
    #
    @60
    @73
    @34
    @57
    cM
    cc0
    wne
    @85
    @64
    cM
    nnne0
    @84
    cM
    cc0
    @82
    @83
    simpr
    necon3ai
    3syl
    @29
    cM
    gcdn0cl
    syl21anc
    #
    nnzd
    #
    @73
    @34
    @4
    @34
    cM
    cN
    @64
    @78
    nnmulcld
    #
    nnzd
    #
    @65
    cM
    @4
    dvdstr
    syl3anc
    mp2and
    @34
    @80
    @56
    @81
    @82
    @4
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @68
    @69
    wa
    @70
    wi
    @88
    @60
    @90
    @34
    @4
    cn
    wcel
    #
    @4
    cc0
    wne
    @93
    @89
    @4
    nnne0
    @92
    @4
    cc0
    @82
    @91
    simpr
    necon3ai
    3syl
    #
    @65
    @29
    @4
    dvdslegcd
    syl31anc
    mp2and
    @33
    @41
    wph
    @33
    @39
    @41
    @44
    simprbi
    adantl
    #
    breqtrd
    @34
    @86
    @66
    @67
    wb
    @87
    @65
    nnle1eq1
    syl
    mpbid
    eqtrd
    @14
    @55
    vy
    @35
    @15
    cU
    @12
    @35
    wceq
    @13
    @54
    c1
    @12
    @35
    cM
    cgcd
    oveq1
    eqeq1d
    phimul.4
    elrab2
    sylanbrc
    @34
    @36
    @21
    wcel
    #
    @36
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @52
    @34
    @56
    @61
    @97
    @60
    @78
    @29
    cN
    zmodfzo
    syl2anc
    @34
    @98
    @29
    cN
    cgcd
    co
    #
    c1
    @34
    @56
    @61
    @98
    @100
    wceq
    @60
    @78
    @29
    cN
    modgcd
    syl2anc
    @34
    @100
    c1
    cle
    wbr
    #
    @100
    c1
    wceq
    #
    @34
    @100
    @40
    c1
    cle
    @34
    @100
    @29
    cdvds
    wbr
    #
    @100
    @4
    cdvds
    wbr
    #
    @100
    @40
    cle
    wbr
    #
    @34
    @103
    @100
    cN
    cdvds
    wbr
    #
    @34
    @56
    @76
    @103
    @106
    wa
    @60
    @79
    @29
    cN
    gcddvds
    syl2anc
    #
    simpld
    @34
    @106
    cN
    @4
    cdvds
    wbr
    #
    @104
    @34
    @103
    @106
    @107
    simprd
    @34
    @72
    @76
    @108
    @73
    @79
    cM
    cN
    dvdsmul2
    syl2anc
    @34
    @100
    cz
    wcel
    #
    @76
    @81
    @106
    @108
    wa
    @104
    wi
    @34
    @100
    @34
    @56
    @76
    @82
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @100
    cn
    wcel
    #
    @60
    @79
    @34
    @61
    cN
    cc0
    wne
    @112
    @78
    cN
    nnne0
    @111
    cN
    cc0
    @82
    @110
    simpr
    necon3ai
    3syl
    @29
    cN
    gcdn0cl
    syl21anc
    #
    nnzd
    #
    @79
    @90
    @100
    cN
    @4
    dvdstr
    syl3anc
    mp2and
    @34
    @109
    @56
    @81
    @93
    @103
    @104
    wa
    @105
    wi
    @115
    @60
    @90
    @95
    @100
    @29
    @4
    dvdslegcd
    syl31anc
    mp2and
    @96
    breqtrd
    @34
    @113
    @101
    @102
    wb
    @114
    @100
    nnle1eq1
    syl
    mpbid
    eqtrd
    @20
    @99
    vy
    @36
    @21
    cV
    @12
    @36
    wceq
    @19
    @98
    c1
    @12
    @36
    cN
    cgcd
    oveq1
    eqeq1d
    phimul.5
    elrab2
    sylanbrc
    @35
    @36
    cU
    cV
    opelxpi
    syl2anc
    eqeltrd
    ralrimiva
    wph
    cF
    wfun
    #
    cW
    cF
    cdm
    #
    wss
    #
    @28
    @32
    wb
    wph
    cS
    cT
    cF
    wf1o
    #
    cF
    cS
    wfn
    #
    @116
    wph
    vx
    cS
    cT
    cF
    cM
    cN
    crth.1
    crth.2
    crth.3
    crth.4
    crth
    #
    cS
    cT
    cF
    f1ofn
    #
    cS
    cF
    fnfun
    3syl
    #
    wph
    cS
    cW
    @117
    cW
    @43
    vy
    cS
    crab
    #
    cS
    phimul.6
    @43
    vy
    cS
    ssrab2
    eqsstri
    #
    wph
    @119
    @120
    @117
    cS
    wceq
    @121
    @122
    cS
    cF
    fndm
    3syl
    syl5sseqr
    #
    vw
    cW
    @8
    cF
    funimass4
    syl2anc
    mpbird
    wph
    vz
    @8
    @27
    wph
    vz
    cv
    #
    @8
    wcel
    #
    @127
    @27
    wcel
    wph
    @128
    wa
    #
    @127
    cF
    ccnv
    #
    cfv
    #
    cF
    cfv
    #
    @127
    @27
    wph
    @119
    @127
    cT
    wcel
    #
    @132
    @127
    wceq
    @128
    @121
    @8
    cT
    @127
    @8
    @15
    @21
    cxp
    #
    cT
    cU
    @15
    wss
    cV
    @21
    wss
    @8
    @134
    wss
    cU
    @16
    @15
    phimul.4
    @17
    eqsstri
    cV
    @22
    @21
    phimul.5
    @23
    eqsstri
    cU
    @15
    cV
    @21
    xpss12
    mp2an
    crth.2
    sseqtr4i
    sseli
    #
    cS
    cT
    @127
    cF
    f1ocnvfv2
    syl2an
    #
    wph
    @128
    @131
    cW
    wcel
    #
    @132
    @27
    wcel
    #
    @129
    @131
    cS
    wcel
    #
    @131
    @4
    cgcd
    co
    #
    c1
    wceq
    #
    @137
    wph
    cT
    cS
    @130
    wf
    #
    @133
    @139
    @128
    wph
    @119
    cT
    cS
    @130
    wf1o
    @142
    @121
    cS
    cT
    cF
    f1ocnv
    cT
    cS
    @130
    f1of
    3syl
    @135
    cT
    cS
    @127
    @130
    ffvelrn
    syl2an
    #
    @129
    @131
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    @131
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @141
    @129
    @131
    cM
    cmo
    co
    #
    cM
    cgcd
    co
    #
    @144
    c1
    @129
    @131
    cz
    wcel
    #
    @57
    @149
    @144
    wceq
    @129
    @131
    @58
    wcel
    @150
    @129
    @131
    cS
    @58
    @143
    crth.1
    syl6eleq
    @131
    cc0
    @4
    elfzoelz
    syl
    #
    wph
    @57
    @128
    @63
    adantr
    @131
    cM
    modgcd
    syl2anc
    @129
    @148
    @15
    wcel
    #
    @149
    c1
    wceq
    #
    @129
    @148
    cU
    wcel
    #
    @152
    @153
    wa
    @129
    @154
    @131
    cN
    cmo
    co
    #
    cV
    wcel
    #
    @129
    @148
    @155
    cop
    #
    @8
    wcel
    @154
    @156
    wa
    @129
    @127
    @157
    @8
    @129
    @132
    @127
    @157
    @136
    @129
    @139
    @132
    @157
    wceq
    @143
    vw
    @131
    @37
    @157
    cS
    cF
    @29
    @131
    wceq
    @35
    @148
    @36
    @155
    @29
    @131
    cM
    cmo
    oveq1
    @29
    @131
    cN
    cmo
    oveq1
    opeq12d
    cF
    vx
    cS
    @49
    cmpt
    vw
    cS
    @37
    cmpt
    crth.3
    vx
    vw
    cS
    @49
    @37
    @50
    cbvmptv
    eqtri
    @148
    @155
    opex
    fvmpt
    syl
    eqtr3d
    wph
    @128
    simpr
    eqeltrrd
    @148
    @155
    cU
    cV
    opelxp
    sylib
    #
    simpld
    @14
    @153
    vy
    @148
    @15
    cU
    @12
    @148
    wceq
    @13
    @149
    c1
    @12
    @148
    cM
    cgcd
    oveq1
    eqeq1d
    phimul.4
    elrab2
    sylib
    simprd
    eqtr3d
    @129
    @155
    cN
    cgcd
    co
    #
    @146
    c1
    @129
    @150
    @61
    @159
    @146
    wceq
    @151
    wph
    @61
    @128
    @77
    adantr
    @131
    cN
    modgcd
    syl2anc
    @129
    @155
    @21
    wcel
    #
    @159
    c1
    wceq
    #
    @129
    @156
    @160
    @161
    wa
    @129
    @154
    @156
    @158
    simprd
    @20
    @161
    vy
    @155
    @21
    cV
    @12
    @155
    wceq
    @19
    @159
    c1
    @12
    @155
    cN
    cgcd
    oveq1
    eqeq1d
    phimul.5
    elrab2
    sylib
    simprd
    eqtr3d
    @129
    @150
    @72
    @76
    @145
    @147
    wa
    @141
    wi
    @151
    wph
    @72
    @128
    wph
    cM
    @63
    nnzd
    adantr
    wph
    @76
    @128
    wph
    cN
    @77
    nnzd
    adantr
    @131
    cM
    cN
    rpmul
    syl3anc
    mp2and
    @43
    @141
    vy
    @131
    cS
    cW
    @12
    @131
    wceq
    @42
    @140
    c1
    @12
    @131
    @4
    cgcd
    oveq1
    eqeq1d
    phimul.6
    elrab2
    sylanbrc
    wph
    @137
    @138
    wph
    @116
    @118
    @137
    @138
    wi
    @123
    @126
    cW
    @131
    cF
    funfvima2
    syl2anc
    imp
    syldan
    eqeltrrd
    ex
    ssrdv
    eqssd
    wph
    cS
    cT
    cF
    wf1
    #
    cW
    cS
    wss
    #
    @27
    cW
    cen
    wbr
    wph
    @119
    @162
    @121
    cS
    cT
    cF
    f1of1
    syl
    @125
    cS
    cT
    cW
    cF
    cW
    cfn
    cS
    cfn
    wcel
    @163
    cW
    cfn
    wcel
    #
    cS
    @58
    cfn
    crth.1
    cc0
    @4
    fzofi
    eqeltri
    @125
    cS
    cW
    ssfi
    mp2an
    #
    elexi
    f1imaen
    sylancl
    eqbrtrrd
    @8
    cfn
    wcel
    #
    @164
    @26
    @25
    wb
    @10
    @11
    @166
    @18
    @24
    cU
    cV
    xpfi
    mp2an
    @165
    @8
    cW
    hashen
    mp2an
    sylibr
    syl5reqr
    wph
    @94
    @5
    @0
    wceq
    wph
    cM
    cN
    @63
    @77
    nnmulcld
    @94
    @5
    @43
    vy
    @58
    crab
    #
    chash
    cfv
    @0
    vy
    @4
    dfphi2
    cW
    @167
    chash
    cW
    @124
    @167
    phimul.6
    cS
    @58
    wceq
    @124
    @167
    wceq
    crth.1
    @43
    vy
    cS
    @58
    rabeq
    ax-mp
    eqtri
    fveq2i
    syl6eqr
    syl
    wph
    @6
    @1
    @7
    @2
    cmul
    wph
    @57
    @6
    @1
    wceq
    @63
    @57
    @6
    @16
    chash
    cfv
    @1
    vy
    cM
    dfphi2
    cU
    @16
    chash
    phimul.4
    fveq2i
    syl6eqr
    syl
    wph
    @61
    @7
    @2
    wceq
    @77
    @61
    @7
    @22
    chash
    cfv
    @2
    vy
    cN
    dfphi2
    cV
    @22
    chash
    phimul.5
    fveq2i
    syl6eqr
    syl
    oveq12d
    3eqtr4d
end
