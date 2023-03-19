include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wf.mm"
include "wtru.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cprime.mm"
include "cc0.mm"
include "cif.mm"
include "wa.mm"
include "nnrecre.mm"
include "adantl.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "serfre.mm"
include "trud.mm"
include "frn.mm"
include "mp1i.mm"
include "1nn.mm"
include "fdmi.mm"
include "eleqtrri.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "climdm.mm"
include "biimpi.mm"
include "a1i.mm"
include "climrecl.mm"
include "simpr.mm"
include "adantr.mm"
include "wceq.mm"
include "weq.mm"
include "eleq1.mm"
include "oveq2.mm"
include "ifbieq1d.mm"
include "prmnn.mm"
include "nnrecred.mm"
include "wn.mm"
include "ifclda.mm"
include "elexi.mm"
include "fvmpt.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "0le0.mm"
include "breq2.mm"
include "ifboth.mm"
include "breqtrrd.mm"
include "climserle.mm"
include "ralrimiva.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "mp2b.mm"
include "rexbii.mm"
include "sylibr.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "2rp.mm"
include "rpreccl.mm"
include "ax-mp.mm"
include "ltsubrp.mm"
include "halfre.mm"
include "resubcl.mm"
include "suprlub.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "rexrn.mm"
include "cmul.mm"
include "cexp.mm"
include "cn0.mm"
include "2re.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "peano2nnd.mm"
include "nnnn0d.mm"
include "reexpcl.mm"
include "ltnrd.mm"
include "cuz.mm"
include "csu.mm"
include "csqrt.mm"
include "cdvds.mm"
include "cfz.mm"
include "cdif.mm"
include "crab.mm"
include "cmpt.mm"
include "peano2nn.mm"
include "nnexpcl.mm"
include "nnsqcld.mm"
include "notbid.mm"
include "cbvralv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "simpll.mm"
include "cbvsumv.mm"
include "syl5eqbr.mm"
include "eqid.mm"
include "prmreclem5.mm"
include "ex.mm"
include "nnzd.mm"
include "eluznn.mm"
include "sylan.mm"
include "syl.mm"
include "simpl.mm"
include "cc.mm"
include "recni.mm"
include "iserex.mm"
include "isumrecl.mm"
include "elfznn.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "ltadd2d.mm"
include "isumsplit.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "bitr4d.mm"
include "isumsup.mm"
include "ltsubaddd.mm"
include "breq12d.mm"
include "3bitr2d.mm"
include "2cn.mm"
include "adddid.mm"
include "nncnd.mm"
include "mulcom.mm"
include "addassd.mm"
include "2timesi.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "3eqtr4d.mm"
include "2nn0.mm"
include "expmuld.mm"
include "expp1.mm"
include "3eqtr3d.mm"
include "expcl.mm"
include "2ne0.mm"
include "divcan4.mm"
include "mp3an23.mm"
include "nnnn0.mm"
include "expaddd.mm"
include "2timesd.mm"
include "nnrpd.mm"
include "rprege0d.mm"
include "sqrtsq.mm"
include "3eqtr4rd.mm"
include "3imtr3d.mm"
include "mtod.mm"
include "nrexdv.mm"
include "pm2.65i.mm"

theorem prmreclem6
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vq: setvar q
  let cK: class K
  let cM: class M
  let cA: class A
  let wph: wff ph
  let cQ: class Q
  let cW: class W
  let cN: class N
  assume prmrec.1: |- F = ( n e. NN |-> if ( n e. Prime , ( 1 / n ) , 0 ) )

  disjoint F n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j r
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k r
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m p
  disjoint m r
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n p
  disjoint n r
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p r
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint j q
  disjoint K j
  disjoint k q
  disjoint K k
  disjoint n q
  disjoint K n
  disjoint p q
  disjoint K p
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint K q
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M k
  disjoint M n
  disjoint M p
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint A r
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint p ph
  disjoint ph q
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Q n
  disjoint Q p
  disjoint Q r
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W j
  disjoint W k
  disjoint W q
  disjoint W x
  disjoint N j
  disjoint N k
  disjoint N n
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- -. seq 1 ( + , F ) e. dom ~~>

  proof
    caddc
    cF
    c1
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    @0
    crn
    #
    cr
    clt
    csup
    #
    c1
    c2
    cdiv
    co
    #
    cmin
    co
    #
    vk
    cv
    #
    @0
    cfv
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @2
    @6
    vy
    cv
    #
    clt
    wbr
    #
    vy
    @3
    wrex
    #
    @10
    @2
    @6
    @4
    clt
    wbr
    #
    @13
    @2
    @4
    cr
    wcel
    #
    @5
    crp
    wcel
    #
    @14
    @2
    @3
    cr
    wss
    #
    @3
    c0
    wne
    #
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vz
    @3
    wral
    #
    vx
    cr
    wrex
    #
    @15
    cn
    cr
    @0
    wf
    #
    @17
    @2
    @24
    wtru
    vj
    cF
    c1
    cn
    nnuz
    wtru
    1zzd
    wtru
    cn
    cr
    vj
    cv
    #
    cF
    wtru
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    c1
    @26
    cdiv
    co
    #
    cc0
    cif
    #
    cr
    cF
    wtru
    @26
    cn
    wcel
    #
    wa
    @28
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @29
    cr
    wcel
    @30
    @31
    wtru
    @26
    nnrecre
    adantl
    0re
    @27
    @28
    cc0
    cr
    ifcl
    sylancl
    prmrec.1
    fmptd
    ffvelrnda
    serfre
    trud
    #
    cn
    cr
    @0
    frn
    mp1i
    #
    c1
    @0
    cdm
    #
    wcel
    #
    @18
    @2
    c1
    cn
    @35
    1nn
    cn
    cr
    @0
    @33
    fdmi
    eleqtrri
    @36
    @35
    c0
    wne
    @18
    @35
    c1
    ne0i
    @35
    c0
    @3
    c0
    @0
    dm0rn0
    necon3bii
    sylib
    mp1i
    #
    @2
    @8
    @20
    cle
    wbr
    #
    vk
    cn
    wral
    #
    vx
    cr
    wrex
    #
    @23
    @2
    @0
    cli
    cfv
    #
    cr
    wcel
    @8
    @41
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @40
    @2
    @41
    vk
    @0
    c1
    cn
    nnuz
    @2
    1zzd
    #
    @2
    @0
    @41
    cli
    wbr
    #
    @0
    climdm
    biimpi
    #
    @2
    cn
    cr
    @7
    @0
    @24
    @2
    @33
    a1i
    ffvelrnda
    #
    climrecl
    @2
    @42
    vk
    cn
    @2
    @7
    cn
    wcel
    #
    wa
    #
    @41
    vj
    cF
    c1
    @7
    cn
    nnuz
    @2
    @48
    simpr
    #
    @2
    @45
    @48
    @46
    adantr
    @2
    @25
    cn
    wcel
    #
    @25
    cF
    cfv
    #
    cr
    wcel
    @48
    @2
    @51
    wa
    #
    @52
    @25
    cprime
    wcel
    #
    c1
    @25
    cdiv
    co
    #
    cc0
    cif
    #
    cr
    @51
    @52
    @56
    wceq
    #
    @2
    vn
    @25
    @29
    @56
    cn
    cF
    vn
    vj
    weq
    @27
    @54
    @28
    @55
    cc0
    @26
    @25
    cprime
    eleq1
    @26
    @25
    c1
    cdiv
    oveq2
    ifbieq1d
    prmrec.1
    @56
    cr
    @56
    cr
    wcel
    #
    wtru
    @54
    @55
    cc0
    cr
    wtru
    @54
    wa
    @25
    @54
    @51
    wtru
    @25
    prmnn
    adantl
    nnrecred
    @32
    wtru
    @54
    wn
    wa
    0re
    a1i
    ifclda
    trud
    #
    elexi
    fvmpt
    #
    adantl
    #
    @58
    @53
    @59
    a1i
    #
    eqeltrd
    adantlr
    @2
    @51
    cc0
    @52
    cle
    wbr
    @48
    @53
    cc0
    @56
    @52
    cle
    @53
    cc0
    @55
    cle
    wbr
    #
    cc0
    cc0
    cle
    wbr
    #
    cc0
    @56
    cle
    wbr
    #
    @53
    @55
    @53
    @25
    @51
    @25
    crp
    wcel
    @2
    @25
    nnrp
    adantl
    rpreccld
    rpge0d
    0le0
    @54
    @63
    @64
    @65
    @55
    cc0
    @55
    @56
    cc0
    cle
    breq2
    cc0
    @56
    cc0
    cle
    breq2
    ifboth
    sylancl
    #
    @61
    breqtrrd
    adantlr
    climserle
    ralrimiva
    @39
    @43
    vx
    @41
    cr
    @20
    @41
    wceq
    @38
    @42
    vk
    cn
    @20
    @41
    @8
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    @22
    @39
    vx
    cr
    @24
    @0
    cn
    wfn
    #
    @22
    @39
    wb
    @33
    cn
    cr
    @0
    ffn
    #
    @21
    @38
    vz
    vk
    cn
    @0
    @19
    @8
    @20
    cle
    breq1
    ralrn
    mp2b
    rexbii
    sylibr
    #
    vx
    vz
    @3
    suprcl
    syl3anc
    #
    c2
    crp
    wcel
    @16
    2rp
    c2
    rpreccl
    ax-mp
    @4
    @5
    ltsubrp
    sylancl
    @2
    @17
    @18
    @23
    @6
    cr
    wcel
    #
    @14
    @13
    wb
    @34
    @37
    @70
    @2
    @15
    @5
    cr
    wcel
    #
    @72
    @71
    halfre
    @4
    @5
    resubcl
    sylancl
    vx
    vz
    vy
    @3
    @6
    suprlub
    syl31anc
    mpbid
    @24
    @68
    @13
    @10
    wb
    @33
    @69
    @12
    @9
    vy
    vk
    cn
    @0
    @11
    @8
    @6
    clt
    breq2
    rexrn
    mp2b
    sylib
    @2
    @9
    vk
    cn
    @49
    @9
    c2
    c2
    @7
    cmul
    co
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    @76
    clt
    wbr
    #
    @49
    @76
    @49
    c2
    cr
    wcel
    @75
    cn0
    wcel
    #
    @76
    cr
    wcel
    2re
    @49
    @75
    @49
    @74
    @49
    c2
    cn
    wcel
    #
    @48
    @74
    cn
    wcel
    2nn
    @50
    c2
    @7
    nnmulcl
    sylancr
    #
    peano2nnd
    nnnn0d
    #
    c2
    @75
    reexpcl
    sylancr
    ltnrd
    @49
    @7
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @56
    vj
    csu
    #
    @5
    clt
    wbr
    #
    c2
    @82
    cexp
    co
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    c2
    @7
    cexp
    co
    #
    @87
    csqrt
    cfv
    #
    cmul
    co
    #
    clt
    wbr
    #
    @9
    @77
    @49
    @85
    @92
    @49
    @85
    wa
    #
    vm
    vn
    cF
    @7
    vp
    cv
    #
    vr
    cv
    #
    cdvds
    wbr
    #
    wn
    #
    vp
    cprime
    c1
    @7
    cfz
    co
    #
    cdif
    #
    wral
    #
    vr
    c1
    @87
    cfz
    co
    #
    crab
    @87
    vw
    cn
    vw
    cv
    #
    cprime
    wcel
    @102
    @26
    cdvds
    wbr
    #
    wa
    vn
    @101
    crab
    cmpt
    #
    vw
    prmrec.1
    @49
    @48
    @85
    @50
    adantr
    @49
    @87
    cn
    wcel
    @85
    @49
    @86
    @49
    @79
    @82
    cn0
    wcel
    @86
    cn
    wcel
    2nn
    @49
    @82
    @48
    @82
    cn
    wcel
    #
    @2
    @7
    peano2nn
    adantl
    #
    nnnn0d
    #
    c2
    @82
    nnexpcl
    sylancr
    #
    nnsqcld
    adantr
    @100
    @103
    wn
    #
    vw
    @99
    wral
    #
    vr
    vn
    @101
    @100
    @102
    @95
    cdvds
    wbr
    #
    wn
    #
    vw
    @99
    wral
    vr
    vn
    weq
    #
    @110
    @97
    @112
    vp
    vw
    @99
    vp
    vw
    weq
    @96
    @111
    @94
    @102
    @95
    cdvds
    breq1
    notbid
    cbvralv
    @113
    @112
    @109
    vw
    @99
    @113
    @111
    @103
    @95
    @26
    @102
    cdvds
    breq2
    notbid
    ralbidv
    syl5bb
    cbvrabv
    @2
    @48
    @85
    simpll
    @93
    @83
    vm
    cv
    #
    cprime
    wcel
    #
    c1
    @114
    cdiv
    co
    #
    cc0
    cif
    #
    vm
    csu
    @84
    @5
    clt
    @83
    @117
    @56
    vm
    vj
    vm
    vj
    weq
    @115
    @54
    @116
    @55
    cc0
    @114
    @25
    cprime
    eleq1
    @114
    @25
    c1
    cdiv
    oveq2
    ifbieq1d
    cbvsumv
    @49
    @85
    simpr
    syl5eqbr
    @104
    eqid
    prmreclem5
    ex
    @49
    @85
    cn
    @56
    vj
    csu
    #
    @98
    @56
    vj
    csu
    #
    @5
    caddc
    co
    #
    clt
    wbr
    #
    @118
    @5
    cmin
    co
    #
    @119
    clt
    wbr
    @9
    @49
    @85
    @119
    @84
    caddc
    co
    #
    @120
    clt
    wbr
    @121
    @49
    @84
    @5
    @119
    @49
    @56
    vj
    cF
    @82
    @83
    @83
    eqid
    #
    @49
    @82
    @106
    nnzd
    @49
    @25
    @83
    wcel
    #
    wa
    #
    @51
    @57
    @49
    @105
    @125
    @51
    @106
    @25
    @82
    eluznn
    sylan
    @60
    syl
    @58
    @126
    @59
    a1i
    @49
    @2
    caddc
    cF
    @82
    cseq
    @1
    wcel
    @2
    @48
    simpl
    #
    @49
    vj
    cF
    c1
    @82
    cn
    nnuz
    @106
    @49
    @51
    wa
    #
    @52
    @56
    cc
    @51
    @57
    @49
    @60
    adantl
    #
    @56
    cc
    wcel
    #
    @128
    @56
    @59
    recni
    #
    a1i
    #
    eqeltrd
    iserex
    mpbid
    isumrecl
    @73
    @49
    halfre
    a1i
    #
    @49
    @119
    @8
    cr
    @49
    @56
    vj
    cF
    c1
    @7
    @49
    @25
    @98
    wcel
    #
    wa
    #
    @51
    @57
    @134
    @51
    @49
    @25
    @7
    elfznn
    adantl
    @60
    syl
    @49
    @7
    cn
    c1
    cuz
    cfv
    @50
    nnuz
    syl6eleq
    @130
    @135
    @131
    a1i
    fsumser
    #
    @47
    eqeltrd
    #
    ltadd2d
    @49
    @118
    @123
    @120
    clt
    @49
    @118
    c1
    @82
    c1
    cmin
    co
    #
    cfz
    co
    #
    @56
    vj
    csu
    #
    @84
    caddc
    co
    @123
    @49
    @56
    vj
    cF
    c1
    @82
    @83
    cn
    nnuz
    @124
    @106
    @129
    @132
    @127
    isumsplit
    @49
    @140
    @119
    @84
    caddc
    @49
    @139
    @98
    @56
    vj
    @49
    @138
    @7
    c1
    cfz
    @49
    @7
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @138
    @7
    wceq
    @48
    @141
    @2
    @7
    nncn
    adantl
    #
    ax-1cn
    @7
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
    breq1d
    bitr4d
    @49
    @118
    @5
    @119
    @2
    @118
    cr
    wcel
    @48
    @2
    @118
    @4
    cr
    @2
    vx
    @56
    vk
    vj
    cF
    @0
    c1
    cn
    nnuz
    @0
    eqid
    @44
    @61
    @62
    @66
    @67
    isumsup
    #
    @71
    eqeltrd
    adantr
    @133
    @137
    ltsubaddd
    @49
    @122
    @6
    @119
    @8
    clt
    @49
    @118
    @4
    @5
    cmin
    @2
    @118
    @4
    wceq
    @48
    @144
    adantr
    oveq1d
    @136
    breq12d
    3bitr2d
    @49
    @88
    @76
    @91
    @76
    clt
    @49
    @88
    @76
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @76
    @49
    @87
    @145
    c2
    cdiv
    @49
    c2
    @82
    c2
    cmul
    co
    #
    cexp
    co
    c2
    @75
    c1
    caddc
    co
    #
    cexp
    co
    #
    @87
    @145
    @49
    @147
    @148
    c2
    cexp
    @49
    c2
    @82
    cmul
    co
    #
    @74
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    @147
    @148
    @49
    c2
    @7
    c1
    c2
    cc
    wcel
    #
    @49
    2cn
    a1i
    #
    @143
    @142
    @49
    ax-1cn
    a1i
    #
    adddid
    @49
    @82
    cc
    wcel
    @153
    @147
    @150
    wceq
    @49
    @82
    @106
    nncnd
    2cn
    @82
    c2
    mulcom
    sylancl
    @49
    @148
    @74
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @152
    @49
    @74
    c1
    c1
    @49
    @74
    @80
    nncnd
    @155
    @155
    addassd
    @151
    @156
    @74
    caddc
    c1
    ax-1cn
    2timesi
    oveq2i
    syl6eqr
    3eqtr4d
    oveq2d
    @49
    c2
    @82
    c2
    @154
    c2
    cn0
    wcel
    @49
    2nn0
    a1i
    @107
    expmuld
    @49
    @153
    @78
    @149
    @145
    wceq
    2cn
    @81
    c2
    @75
    expp1
    sylancr
    3eqtr3d
    oveq1d
    @49
    @76
    cc
    wcel
    #
    @146
    @76
    wceq
    #
    @49
    @153
    @78
    @157
    2cn
    @81
    c2
    @75
    expcl
    sylancr
    @157
    @153
    c2
    cc0
    wne
    @158
    2cn
    2ne0
    @76
    c2
    divcan4
    mp3an23
    syl
    eqtrd
    @49
    c2
    @7
    @82
    caddc
    co
    #
    cexp
    co
    @89
    @86
    cmul
    co
    @76
    @91
    @49
    c2
    @7
    @82
    @154
    @107
    @48
    @7
    cn0
    wcel
    @2
    @7
    nnnn0
    adantl
    expaddd
    @49
    @75
    @159
    c2
    cexp
    @49
    @75
    @7
    @7
    caddc
    co
    #
    c1
    caddc
    co
    @159
    @49
    @74
    @160
    c1
    caddc
    @49
    @7
    @143
    2timesd
    oveq1d
    @49
    @7
    @7
    c1
    @143
    @143
    @155
    addassd
    eqtrd
    oveq2d
    @49
    @90
    @86
    @89
    cmul
    @49
    @86
    cr
    wcel
    cc0
    @86
    cle
    wbr
    wa
    @90
    @86
    wceq
    @49
    @86
    @49
    @86
    @108
    nnrpd
    rprege0d
    @86
    sqrtsq
    syl
    oveq2d
    3eqtr4rd
    breq12d
    3imtr3d
    mtod
    nrexdv
    pm2.65i
end
