include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cc.mm"
include "ccncf.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wcel.mm"
include "wral.mm"
include "abelthlem4.mm"
include "wa.mm"
include "c1.mm"
include "wceq.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "crp.mm"
include "wrex.mm"
include "abelthlem9.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "cbl.mm"
include "wss.mm"
include "abelthlem2.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "ovresd.mm"
include "ax-1cn.mm"
include "cmul.mm"
include "cle.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "cxmt.mm"
include "wb.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "mp2an.mm"
include "a1i.mm"
include "cmopn.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "metcnp.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wne.mm"
include "eldifsn.mm"
include "ccnv.mm"
include "caddc.mm"
include "cn0.mm"
include "cexp.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cr.mm"
include "cxr.mm"
include "csup.mm"
include "cico.mm"
include "cima.mm"
include "csu.mm"
include "simprd.mm"
include "w3a.mm"
include "abscl.mm"
include "adantl.mm"
include "a1d.mm"
include "absge0.mm"
include "abelthlem1.mm"
include "rexrd.mm"
include "1re.mm"
include "rexr.mm"
include "mp1i.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "xrltletr.mm"
include "mpan2d.mm"
include "3jcad.mm"
include "0cn.mm"
include "mpan.mm"
include "abssub.mm"
include "subid1.mm"
include "3eqtrd.mm"
include "0re.mm"
include "elico2.mm"
include "3imtr4d.mm"
include "imdistanda.mm"
include "rexri.mm"
include "elbl.mm"
include "mp3an.mm"
include "wfn.mm"
include "absf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "sstrd.mm"
include "resmptd.mm"
include "reseq1i.mm"
include "difss.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "cnvimass.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "sseli.mm"
include "pserval2.mm"
include "sumeq2dv.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "syl6reqr.mm"
include "syl.mm"
include "mpteq2ia.mm"
include "psercn.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "sstri.mm"
include "ssid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "syl6eleq.mm"
include "ctopon.mm"
include "resttopon.mm"
include "cncnpi.mm"
include "cvv.mm"
include "cnex.mm"
include "ssexi.mm"
include "restabs.mm"
include "oveq1i.mm"
include "fveq1i.mm"
include "syl6eleqr.mm"
include "cnt.mm"
include "resttop.mm"
include "ccld.mm"
include "snssd.mm"
include "cha.mm"
include "cnfldhaus.mm"
include "sncld.mm"
include "restcldi.mm"
include "mp3an12.mm"
include "cuni.mm"
include "restuni.mm"
include "cldopn.mm"
include "3syl.mm"
include "isopn3.mm"
include "sylib.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "cncnp.mm"
include "sylanbrc.mm"

theorem abelth
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let cR: class R
  let vr: setvar r
  let cX: class X
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )

  disjoint n x
  disjoint n z
  disjoint M n
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint A n
  disjoint A x
  disjoint A z
  disjoint n ph
  disjoint ph x
  disjoint S n
  disjoint S x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint M k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint y z
  disjoint M y
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint n r
  disjoint X n
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
  disjoint A k
  disjoint m r
  disjoint m t
  disjoint m v
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S r
  disjoint S w
  disjoint S y
  assert |- ( ph -> F e. ( S -cn-> CC ) )

  proof
    wph
    cF
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @0
    ccn
    co
    #
    cS
    cc
    ccncf
    co
    #
    wph
    cS
    cc
    cF
    wf
    #
    cF
    vy
    cv
    #
    @1
    @0
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vy
    cS
    wral
    #
    cF
    @2
    wcel
    #
    wph
    vx
    vz
    cA
    cS
    vn
    cF
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelthlem4
    #
    wph
    @8
    vy
    cS
    wph
    @5
    cS
    wcel
    #
    wa
    #
    @8
    @5
    c1
    @13
    @5
    c1
    wceq
    #
    wa
    #
    cF
    c1
    @6
    cfv
    #
    @7
    wph
    cF
    @16
    wcel
    #
    @12
    @14
    wph
    @17
    @4
    c1
    @5
    cabs
    cmin
    ccom
    #
    cS
    cS
    cxp
    cres
    #
    co
    #
    vw
    cv
    #
    clt
    wbr
    #
    c1
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @18
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vw
    crp
    wrex
    #
    vr
    crp
    wral
    #
    @11
    wph
    @30
    vr
    crp
    wph
    @26
    crp
    wcel
    #
    wa
    #
    @30
    c1
    @5
    cmin
    co
    cabs
    cfv
    #
    @21
    clt
    wbr
    #
    @23
    @24
    cmin
    co
    cabs
    cfv
    #
    @26
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vw
    crp
    wrex
    wph
    vx
    vy
    vz
    vw
    cA
    @26
    cS
    vn
    cF
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelthlem9
    @33
    @29
    @39
    vw
    crp
    @33
    @28
    @38
    vy
    cS
    @33
    @12
    wa
    #
    @22
    @35
    @27
    @37
    @40
    @20
    @34
    @21
    clt
    @40
    @20
    c1
    @5
    @18
    co
    #
    @34
    @40
    c1
    @5
    @18
    cS
    wph
    c1
    cS
    wcel
    #
    @32
    @12
    wph
    @42
    cS
    c1
    csn
    #
    cdif
    #
    cc0
    c1
    @18
    cbl
    cfv
    co
    #
    wss
    #
    wph
    vz
    cA
    cS
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelthlem2
    #
    simpld
    #
    ad2antrr
    #
    @33
    @12
    simpr
    #
    ovresd
    @40
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    @41
    @34
    wceq
    ax-1cn
    @40
    cS
    cc
    @5
    cS
    c1
    vz
    cv
    #
    cmin
    co
    cabs
    cfv
    cM
    c1
    @52
    cabs
    cfv
    cmin
    co
    cmul
    co
    cle
    wbr
    #
    vz
    cc
    crab
    cc
    abelth.5
    @53
    vz
    cc
    ssrab2
    eqsstri
    #
    @50
    sseldi
    c1
    @5
    @18
    @18
    eqid
    #
    cnmetdval
    sylancr
    eqtrd
    breq1d
    @40
    @25
    @36
    @26
    clt
    @40
    @23
    cc
    wcel
    @24
    cc
    wcel
    @25
    @36
    wceq
    @40
    cS
    cc
    c1
    cF
    wph
    @4
    @32
    @12
    @11
    ad2antrr
    @49
    ffvelrnd
    @33
    cS
    cc
    @5
    cF
    wph
    @4
    @32
    @11
    adantr
    ffvelrnda
    @23
    @24
    @18
    @55
    cnmetdval
    syl2anc
    breq1d
    imbi12d
    ralbidva
    rexbidv
    mpbird
    ralrimiva
    wph
    @19
    cS
    cxmt
    cfv
    wcel
    #
    @18
    cc
    cxmt
    cfv
    wcel
    #
    @42
    @17
    @4
    @31
    wa
    wb
    @56
    wph
    @57
    cS
    cc
    wss
    #
    @56
    cnxmet
    @54
    @18
    cS
    cc
    xmetres2
    mp2an
    a1i
    @57
    wph
    cnxmet
    a1i
    @48
    vr
    vw
    vy
    @19
    @18
    c1
    cF
    @1
    @0
    cS
    cc
    @57
    @58
    @1
    @19
    cmopn
    cfv
    #
    wceq
    cnxmet
    @54
    @18
    @19
    @0
    @59
    cc
    cS
    @19
    eqid
    @0
    @0
    eqid
    #
    cnfldtopn
    #
    @59
    eqid
    metrest
    mp2an
    @61
    metcnp
    syl3anc
    mpbir2and
    ad2antrr
    @15
    @5
    c1
    @6
    @13
    @14
    simpr
    fveq2d
    eleqtrrd
    wph
    @12
    @5
    c1
    wne
    #
    @8
    @12
    @62
    wa
    wph
    @5
    @44
    wcel
    #
    @8
    @5
    cS
    c1
    eldifsn
    wph
    @63
    wa
    #
    @8
    cF
    @44
    cres
    #
    @5
    @1
    @44
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @64
    @65
    @5
    @0
    @44
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    @68
    @64
    @65
    @70
    @0
    ccn
    co
    #
    wcel
    @63
    @65
    @72
    wcel
    @64
    @65
    @44
    cc
    ccncf
    co
    #
    @73
    wph
    @65
    @74
    wcel
    @63
    wph
    vx
    cabs
    ccnv
    cc0
    caddc
    @26
    vt
    cc
    vn
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    vt
    cv
    @75
    cexp
    co
    cmul
    co
    cmpt
    cmpt
    #
    cfv
    cc0
    cseq
    cli
    cdm
    wcel
    vr
    cr
    crab
    cxr
    clt
    csup
    #
    cico
    co
    #
    cima
    #
    cn0
    @76
    vx
    cv
    #
    @75
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cmpt
    #
    @44
    cres
    #
    @65
    @74
    wph
    @86
    vx
    @44
    @84
    cmpt
    #
    @65
    wph
    vx
    @80
    @44
    @84
    wph
    @44
    @45
    @80
    wph
    @42
    @46
    @47
    simprd
    wph
    vw
    @45
    @80
    wph
    @21
    cc
    wcel
    #
    cc0
    @21
    @18
    co
    #
    c1
    clt
    wbr
    #
    wa
    #
    @88
    @21
    cabs
    cfv
    #
    @79
    wcel
    #
    wa
    #
    @21
    @45
    wcel
    #
    @21
    @80
    wcel
    #
    wph
    @88
    @90
    @93
    wph
    @88
    wa
    #
    @92
    c1
    clt
    wbr
    #
    @92
    cr
    wcel
    #
    cc0
    @92
    cle
    wbr
    #
    @92
    @78
    clt
    wbr
    #
    w3a
    #
    @90
    @93
    @97
    @98
    @99
    @100
    @101
    @97
    @99
    @98
    @88
    @99
    wph
    @21
    abscl
    adantl
    #
    a1d
    @97
    @100
    @98
    @88
    @100
    wph
    @21
    absge0
    adantl
    a1d
    @97
    @98
    c1
    @78
    cle
    wbr
    #
    @101
    wph
    @104
    @88
    wph
    vt
    cA
    vn
    vr
    abelth.1
    abelth.2
    abelthlem1
    adantr
    @97
    @92
    cxr
    wcel
    c1
    cxr
    wcel
    #
    @78
    cxr
    wcel
    #
    @98
    @104
    wa
    @101
    wi
    @97
    @92
    @103
    rexrd
    c1
    cr
    wcel
    @105
    @97
    1re
    c1
    rexr
    mp1i
    wph
    @106
    @88
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    @78
    cc0
    cpnf
    iccssxr
    wph
    vt
    cA
    @78
    vn
    @77
    vr
    @77
    eqid
    #
    abelth.1
    @78
    eqid
    #
    radcnvcl
    sseldi
    adantr
    #
    @92
    c1
    @78
    xrltletr
    syl3anc
    mpan2d
    3jcad
    @88
    @90
    @98
    wb
    wph
    @88
    @89
    @92
    c1
    clt
    @88
    @89
    cc0
    @21
    cmin
    co
    cabs
    cfv
    #
    @21
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @92
    cc0
    cc
    wcel
    #
    @88
    @89
    @110
    wceq
    0cn
    cc0
    @21
    @18
    @55
    cnmetdval
    mpan
    @113
    @88
    @110
    @112
    wceq
    0cn
    cc0
    @21
    abssub
    mpan
    @88
    @111
    @21
    cabs
    @21
    subid1
    fveq2d
    3eqtrd
    breq1d
    adantl
    @97
    cc0
    cr
    wcel
    @106
    @93
    @102
    wb
    0re
    @109
    cc0
    @78
    @92
    elico2
    sylancr
    3imtr4d
    imdistanda
    @57
    @113
    @105
    @95
    @91
    wb
    cnxmet
    0cn
    c1
    1re
    rexri
    @21
    @18
    cc0
    c1
    cc
    elbl
    mp3an
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @96
    @94
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @21
    @79
    cabs
    elpreima
    mp2b
    3imtr4g
    ssrdv
    sstrd
    #
    resmptd
    @65
    vx
    cS
    @84
    cmpt
    #
    @44
    cres
    #
    @87
    cF
    @115
    @44
    abelth.6
    reseq1i
    @44
    cS
    wss
    #
    @116
    @87
    wceq
    cS
    @43
    difss
    #
    vx
    cS
    @44
    @84
    resmpt
    ax-mp
    eqtri
    syl6eqr
    wph
    @44
    @80
    wss
    @85
    @80
    cc
    ccncf
    co
    wcel
    @86
    @74
    wcel
    @114
    wph
    vt
    vx
    cA
    @78
    @80
    vj
    vn
    @85
    @77
    @78
    cr
    wcel
    vv
    cv
    cabs
    cfv
    #
    @78
    caddc
    co
    c2
    cdiv
    co
    @119
    c1
    caddc
    co
    cif
    #
    vr
    vv
    @107
    vx
    @80
    @84
    cn0
    vj
    cv
    #
    @81
    @77
    cfv
    cfv
    #
    vj
    csu
    #
    @81
    @80
    wcel
    @81
    cc
    wcel
    #
    @84
    @123
    wceq
    @80
    cc
    @81
    @80
    cabs
    cdm
    cc
    cabs
    @79
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    sseli
    @124
    @123
    cn0
    @121
    cA
    cfv
    #
    @81
    @121
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    @84
    @124
    cn0
    @122
    @127
    vj
    vt
    cA
    vn
    @77
    @121
    @81
    @107
    pserval2
    sumeq2dv
    cn0
    @83
    @127
    vn
    vj
    @75
    @121
    wceq
    @76
    @125
    @82
    @126
    cmul
    @75
    @121
    cA
    fveq2
    @75
    @121
    @81
    cexp
    oveq2
    oveq12d
    cbvsumv
    syl6reqr
    syl
    mpteq2ia
    abelth.1
    @108
    @80
    eqid
    @120
    eqid
    psercn
    @80
    cc
    @44
    @85
    rescncf
    sylc
    eqeltrrd
    adantr
    @44
    cc
    wss
    #
    cc
    cc
    wss
    #
    @74
    @73
    wceq
    @44
    cS
    cc
    @118
    @54
    sstri
    #
    cc
    ssid
    #
    @44
    cc
    @0
    @70
    @0
    @60
    @70
    eqid
    @0
    cc
    crest
    co
    #
    @0
    @0
    ctop
    wcel
    #
    @132
    @0
    wceq
    @0
    @60
    cnfldtop
    #
    @0
    ctop
    cc
    cc
    @0
    @0
    @60
    cnfldtopon
    #
    toponunii
    #
    restid
    ax-mp
    eqcomi
    #
    cncfcn
    mp2an
    syl6eleq
    wph
    @63
    simpr
    @5
    @65
    @70
    @0
    @44
    @44
    @70
    @0
    cc
    ctopon
    cfv
    wcel
    #
    @128
    @70
    @44
    ctopon
    cfv
    wcel
    @135
    @130
    @44
    @0
    cc
    resttopon
    mp2an
    toponunii
    cncnpi
    syl2anc
    @5
    @67
    @71
    @66
    @70
    @0
    ccnp
    @133
    @117
    cS
    cvv
    wcel
    #
    @66
    @70
    wceq
    @134
    @118
    cS
    cc
    cnex
    @54
    ssexi
    #
    @44
    cS
    @0
    ctop
    cvv
    restabs
    mp3an
    oveq1i
    fveq1i
    syl6eleqr
    @64
    @1
    ctop
    wcel
    #
    @117
    @5
    @44
    @1
    cnt
    cfv
    cfv
    #
    wcel
    #
    @4
    @8
    @69
    wb
    @141
    @64
    @133
    @139
    @141
    @134
    @140
    cS
    @0
    cvv
    resttop
    mp2an
    #
    a1i
    @117
    @64
    @118
    a1i
    wph
    @143
    @63
    wph
    @142
    @44
    @5
    wph
    @44
    @1
    wcel
    #
    @142
    @44
    wceq
    #
    wph
    @43
    cS
    wss
    #
    @43
    @1
    ccld
    cfv
    wcel
    #
    @145
    wph
    c1
    cS
    @48
    snssd
    @58
    @43
    @0
    ccld
    cfv
    wcel
    #
    @147
    @148
    @54
    @0
    cha
    wcel
    @51
    @149
    @0
    @60
    cnfldhaus
    ax-1cn
    c1
    @0
    cc
    @136
    sncld
    mp2an
    cS
    @43
    @0
    cc
    @136
    restcldi
    mp3an12
    @43
    @1
    cS
    @133
    @58
    cS
    @1
    cuni
    wceq
    @134
    @54
    cS
    @0
    cc
    @136
    restuni
    mp2an
    #
    cldopn
    3syl
    @141
    @117
    @145
    @146
    wb
    @144
    @118
    @44
    @1
    cS
    @150
    isopn3
    mp2an
    sylib
    eleq2d
    biimpar
    wph
    @4
    @63
    @11
    adantr
    @44
    @5
    cF
    @1
    @0
    cS
    cc
    @150
    @136
    cnprest
    syl22anc
    mpbird
    sylan2br
    anassrs
    pm2.61dane
    ralrimiva
    @1
    cS
    ctopon
    cfv
    wcel
    #
    @138
    @10
    @4
    @9
    wa
    wb
    @138
    @58
    @151
    @135
    @54
    cS
    @0
    cc
    resttopon
    mp2an
    @135
    vy
    cF
    @1
    @0
    cS
    cc
    cncnp
    mp2an
    sylanbrc
    @58
    @129
    @3
    @2
    wceq
    @54
    @131
    cS
    cc
    @0
    @1
    @0
    @60
    @1
    eqid
    @137
    cncfcn
    mp2an
    syl6eleqr
end
