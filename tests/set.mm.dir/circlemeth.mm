include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "cfzo.mm"
include "cv.mm"
include "cfv.mm"
include "cvts.mm"
include "cprod.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "cneg.mm"
include "ce.mm"
include "citg.mm"
include "cfz.mm"
include "crepr.mm"
include "cmin.mm"
include "csu.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "adantr.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "sselda.mm"
include "nnnn0d.mm"
include "cmap.mm"
include "wf.mm"
include "vtsprod.mm"
include "oveq1d.mm"
include "fzfid.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "nn0cnd.mm"
include "negcld.mm"
include "ralrimivw.mm"
include "r19.21bi.mm"
include "mulcld.mm"
include "efcld.mm"
include "fz1ssnn.mm"
include "cz.mm"
include "fzssz.mm"
include "simpr.mm"
include "sseldi.mm"
include "adantlr.mm"
include "reprfi.mm"
include "cfn.mm"
include "fzofi.mm"
include "ad3antrrr.mm"
include "zcnd.mm"
include "ad2antrr.mm"
include "reprf.mm"
include "ffvelrnda.mm"
include "breprexplemb.mm"
include "adantl3r.mm"
include "fprodcl.mm"
include "fsumcl.mm"
include "fsummulc1.mm"
include "mulassd.mm"
include "wceq.mm"
include "caddc.mm"
include "efadd.mm"
include "syl2anc.mm"
include "adddid.mm"
include "adddird.mm"
include "negsubd.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "3eqtrd.mm"
include "itgeq2dv.mm"
include "cmpt.mm"
include "cibl.mm"
include "cvv.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "sumex.mm"
include "adantllr.mm"
include "subcld.mm"
include "an32s.mm"
include "anasss.mm"
include "fvex.mm"
include "cicc.mm"
include "ioossicc.mm"
include "ccncf.mm"
include "0red.mm"
include "1red.mm"
include "unitsscn.mm"
include "ssid.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "cncfmptid.mm"
include "mulcncf.mm"
include "efmul2picn.mm"
include "cniccibl.mm"
include "iblss.mm"
include "iblmulc2.mm"
include "itgfsum.mm"
include "simpld.mm"
include "simprd.mm"
include "csn.mm"
include "cif.mm"
include "oveq2.mm"
include "mulid1d.mm"
include "mul01d.mm"
include "ifeq3da.mm"
include "subeq0ad.mm"
include "velsn.mm"
include "syl6rbbr.mm"
include "ifbid.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "itgexpif.mm"
include "syl.mm"
include "1cnd.mm"
include "0cnd.mm"
include "ifcld.mm"
include "eqtr4d.mm"
include "3eqtr4rd.mm"
include "wral.mm"
include "cuz.mm"
include "wo.mm"
include "cle.mm"
include "wbr.mm"
include "0zd.mm"
include "zmulcld.mm"
include "nn0ge0d.mm"
include "nnmulge.mm"
include "elfz4.mm"
include "syl32anc.mm"
include "snssd.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "sumeq1d.mm"
include "sumsn.mm"
include "3eqtr2d.mm"
include "itgmulc2.mm"
include "reprfz1.mm"
include "3eqtr4d.mm"
include "3eqtrrd.mm"

theorem circlemeth
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cL: class L
  let cN: class N
  let va: setvar a
  let vc: setvar c
  let vm: setvar m
  assume circlemeth.n: |- ( ph -> N e. NN0 )
  assume circlemeth.s: |- ( ph -> S e. NN )
  assume circlemeth.l: |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) )

  disjoint L a
  disjoint L c
  disjoint L x
  disjoint a c
  disjoint a x
  disjoint c x
  disjoint N a
  disjoint N c
  disjoint N x
  disjoint S a
  disjoint S c
  disjoint S x
  disjoint a ph
  disjoint c ph
  disjoint ph x
  disjoint L m
  disjoint a m
  disjoint c m
  disjoint m x
  disjoint N m
  disjoint S m
  disjoint m ph
  assert |- ( ph -> sum_ c e. ( NN ( repr ` S ) N ) prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( c ` a ) ) = S. ( 0 (,) 1 ) ( prod_ a e. ( 0 ..^ S ) ( ( ( L ` a ) vts N ) ` x ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x )

  proof
    wph
    vx
    cc0
    c1
    cioo
    co
    #
    cc0
    cS
    cfzo
    co
    #
    vx
    cv
    #
    va
    cv
    #
    cL
    cfv
    #
    cN
    cvts
    co
    cfv
    va
    cprod
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cN
    cneg
    #
    @2
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    citg
    vx
    @0
    cc0
    cS
    cN
    cmul
    co
    #
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    vm
    cv
    #
    cS
    crepr
    cfv
    #
    co
    #
    @1
    @3
    vc
    cv
    #
    cfv
    #
    @4
    cfv
    #
    va
    cprod
    #
    @7
    @16
    cN
    cmin
    co
    #
    @2
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    citg
    #
    @14
    vx
    @0
    @28
    citg
    #
    vm
    csu
    #
    cn
    cN
    @17
    co
    #
    @22
    vc
    csu
    #
    wph
    vx
    @0
    @12
    @29
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @12
    @14
    @18
    @22
    @7
    @16
    @2
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    @11
    cmul
    co
    @14
    @41
    @11
    cmul
    co
    #
    vm
    csu
    @29
    @36
    @5
    @42
    @11
    cmul
    @36
    cS
    vm
    cL
    cN
    @2
    va
    vc
    wph
    cN
    cn0
    wcel
    #
    @35
    circlemeth.n
    adantr
    wph
    @0
    cc
    @2
    @0
    cc
    wss
    wph
    @0
    cr
    cc
    cc0
    c1
    ioossre
    ax-resscn
    sstri
    a1i
    sselda
    #
    wph
    cS
    cn0
    wcel
    #
    @35
    wph
    cS
    circlemeth.s
    nnnn0d
    #
    adantr
    #
    wph
    @1
    cc
    cn
    cmap
    co
    cL
    wf
    #
    @35
    circlemeth.l
    adantr
    vtsprod
    oveq1d
    @36
    @14
    @41
    @11
    vm
    @36
    cc0
    @13
    fzfid
    @36
    @10
    @36
    @7
    @9
    @7
    cc
    wcel
    #
    @36
    ci
    @6
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    mulcli
    #
    a1i
    @36
    @8
    @2
    wph
    @8
    cc
    wcel
    #
    vx
    @0
    wph
    @52
    vx
    @0
    wph
    cN
    wph
    cN
    circlemeth.n
    nn0cnd
    #
    negcld
    ralrimivw
    r19.21bi
    #
    @45
    mulcld
    #
    mulcld
    #
    efcld
    #
    @36
    @16
    @14
    wcel
    #
    wa
    #
    @18
    @40
    vc
    @59
    @15
    cS
    @16
    @15
    cn
    wss
    #
    @59
    cN
    fz1ssnn
    #
    a1i
    wph
    @58
    @16
    cz
    wcel
    #
    @35
    wph
    @58
    wa
    #
    @14
    cz
    @16
    cc0
    @13
    fzssz
    wph
    @58
    simpr
    sseldi
    #
    adantlr
    #
    @36
    @46
    @58
    @48
    adantr
    @59
    c1
    cN
    fzfid
    reprfi
    #
    @59
    @19
    @18
    wcel
    #
    wa
    #
    @22
    @39
    @68
    @1
    @21
    va
    @1
    cfn
    wcel
    #
    @68
    cc0
    cS
    fzofi
    #
    a1i
    wph
    @35
    @58
    @67
    @3
    @1
    wcel
    #
    @21
    cc
    wcel
    #
    @63
    @67
    wa
    #
    @71
    wa
    #
    cS
    cL
    cN
    @3
    @20
    @16
    wph
    @44
    @58
    @67
    @71
    circlemeth.n
    ad3antrrr
    wph
    @46
    @58
    @67
    @71
    @47
    ad3antrrr
    @63
    @16
    cc
    wcel
    @67
    @71
    @63
    @16
    @64
    zcnd
    #
    ad2antrr
    wph
    @49
    @58
    @67
    @71
    circlemeth.l
    ad3antrrr
    @73
    @71
    simpr
    @74
    @15
    cn
    @20
    @61
    @73
    @1
    @15
    @3
    @19
    @73
    @15
    @19
    cS
    @16
    @60
    @73
    @61
    a1i
    @63
    @62
    @67
    @64
    adantr
    #
    wph
    @46
    @58
    @67
    @47
    ad2antrr
    @63
    @67
    simpr
    reprf
    ffvelrnda
    sseldi
    breprexplemb
    #
    adantl3r
    fprodcl
    #
    @59
    @39
    cc
    wcel
    @67
    @59
    @38
    @59
    @7
    @37
    @50
    @59
    @51
    a1i
    #
    @59
    @16
    @2
    @59
    @16
    @65
    zcnd
    #
    @36
    @2
    cc
    wcel
    @58
    @45
    adantr
    #
    mulcld
    #
    mulcld
    #
    efcld
    adantr
    #
    mulcld
    #
    fsumcl
    fsummulc1
    @36
    @14
    @43
    @28
    vm
    @59
    @43
    @18
    @40
    @11
    cmul
    co
    #
    vc
    csu
    @28
    @59
    @18
    @40
    @11
    vc
    @66
    @36
    @11
    cc
    wcel
    #
    @58
    @57
    adantr
    #
    @85
    fsummulc1
    @59
    @18
    @86
    @27
    vc
    @68
    @86
    @22
    @39
    @11
    cmul
    co
    #
    cmul
    co
    #
    @27
    @68
    @22
    @39
    @11
    @78
    @84
    @59
    @87
    @67
    @88
    adantr
    mulassd
    @59
    @90
    @27
    wceq
    @67
    @59
    @89
    @26
    @22
    cmul
    @59
    @38
    @10
    caddc
    co
    #
    ce
    cfv
    #
    @89
    @26
    @59
    @38
    cc
    wcel
    @10
    cc
    wcel
    #
    @92
    @89
    wceq
    @83
    @36
    @93
    @58
    @56
    adantr
    @38
    @10
    efadd
    syl2anc
    @59
    @91
    @25
    ce
    @59
    @7
    @37
    @9
    caddc
    co
    #
    cmul
    co
    @91
    @25
    @59
    @7
    @37
    @9
    @79
    @82
    @36
    @9
    cc
    wcel
    @58
    @55
    adantr
    adddid
    @59
    @94
    @24
    @7
    cmul
    @59
    @16
    @8
    caddc
    co
    #
    @2
    cmul
    co
    @94
    @24
    @59
    @16
    @8
    @2
    @80
    @36
    @52
    @58
    @54
    adantr
    @81
    adddird
    @59
    @95
    @23
    @2
    cmul
    @59
    @16
    cN
    @80
    wph
    cN
    cc
    wcel
    #
    @35
    @58
    @53
    ad2antrr
    #
    negsubd
    oveq1d
    eqtr3d
    oveq2d
    eqtr3d
    fveq2d
    eqtr3d
    oveq2d
    adantr
    eqtrd
    sumeq2dv
    eqtrd
    sumeq2dv
    3eqtrd
    itgeq2dv
    wph
    vx
    @0
    @29
    cmpt
    cibl
    wcel
    @30
    @32
    wceq
    wph
    vx
    @0
    @14
    @28
    vm
    cvv
    @0
    cvol
    cdm
    wcel
    #
    wph
    cc0
    c1
    ioombl
    #
    a1i
    #
    wph
    cc0
    @13
    fzfid
    #
    @28
    cvv
    wcel
    wph
    @35
    @58
    wa
    wa
    @18
    @27
    vc
    sumex
    a1i
    @63
    vx
    @0
    @28
    cmpt
    cibl
    wcel
    #
    @31
    @18
    vx
    @0
    @27
    citg
    #
    vc
    csu
    #
    wceq
    #
    @63
    vx
    @0
    @18
    @27
    vc
    cc
    wph
    @98
    @58
    @100
    adantr
    @63
    @15
    cS
    @16
    @60
    @63
    @61
    a1i
    @64
    wph
    @46
    @58
    @47
    adantr
    @63
    c1
    cN
    fzfid
    reprfi
    #
    @63
    @35
    @67
    @27
    cc
    wcel
    @63
    @35
    wa
    #
    @67
    wa
    #
    @22
    @26
    @108
    @1
    @21
    va
    @69
    @108
    @70
    a1i
    @63
    @67
    @71
    @72
    @35
    @77
    adantllr
    fprodcl
    @108
    @25
    @107
    @25
    cc
    wcel
    #
    @67
    wph
    @35
    @58
    @109
    @59
    @7
    @24
    @79
    @59
    @23
    @2
    @59
    @16
    cN
    @80
    @97
    subcld
    @81
    mulcld
    mulcld
    an32s
    adantr
    efcld
    #
    mulcld
    anasss
    @73
    vx
    @0
    @26
    @22
    cvv
    @73
    @1
    @21
    va
    @69
    @73
    @70
    a1i
    @77
    fprodcl
    #
    @26
    cvv
    wcel
    #
    @73
    @35
    wa
    @25
    ce
    fvex
    #
    a1i
    @63
    vx
    @0
    @26
    cmpt
    cibl
    wcel
    @67
    @63
    vx
    @0
    cc0
    c1
    cicc
    co
    #
    @26
    cvv
    @0
    @114
    wss
    @63
    cc0
    c1
    ioossicc
    a1i
    @98
    @63
    @99
    a1i
    @112
    @63
    @2
    @114
    wcel
    wa
    @113
    a1i
    @63
    cc0
    cr
    wcel
    c1
    cr
    wcel
    vx
    @114
    @26
    cmpt
    #
    @114
    cc
    ccncf
    co
    #
    wcel
    @115
    cibl
    wcel
    @63
    0red
    @63
    1red
    @63
    vx
    @114
    @24
    @63
    vx
    @23
    @2
    @114
    @63
    @23
    cc
    wcel
    @114
    cc
    wss
    #
    cc
    cc
    wss
    #
    vx
    @114
    @23
    cmpt
    @116
    wcel
    @63
    @16
    cN
    @75
    wph
    @96
    @58
    @53
    adantr
    #
    subcld
    @117
    @63
    unitsscn
    a1i
    #
    @118
    @63
    cc
    ssid
    a1i
    #
    vx
    @23
    @114
    cc
    cncfmptc
    syl3anc
    @63
    @117
    @118
    vx
    @114
    @2
    cmpt
    @116
    wcel
    @120
    @121
    vx
    @114
    cc
    cncfmptid
    syl2anc
    mulcncf
    efmul2picn
    cc0
    c1
    @115
    cniccibl
    syl3anc
    iblss
    adantr
    #
    iblmulc2
    itgfsum
    #
    simpld
    itgfsum
    simprd
    wph
    @14
    @18
    @22
    vx
    @0
    @26
    citg
    #
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    @15
    cN
    @17
    co
    #
    @22
    vc
    csu
    #
    @32
    @34
    wph
    @127
    @14
    @16
    cN
    csn
    #
    wcel
    #
    @18
    @22
    vc
    csu
    #
    cc0
    cif
    #
    vm
    csu
    #
    @130
    @132
    vm
    csu
    #
    @129
    wph
    @14
    @126
    @133
    vm
    @63
    @23
    cc0
    wceq
    #
    @132
    cc0
    cif
    @132
    @136
    c1
    cc0
    cif
    #
    cmul
    co
    #
    @133
    @126
    @63
    @136
    @132
    cc0
    @138
    c1
    cc0
    @132
    c1
    cmul
    co
    @132
    cc0
    cmul
    co
    @137
    c1
    @132
    cmul
    oveq2
    @137
    cc0
    @132
    cmul
    oveq2
    @63
    @132
    @63
    @18
    @22
    vc
    @106
    @111
    fsumcl
    #
    mulid1d
    @63
    @132
    @139
    mul01d
    ifeq3da
    @63
    @131
    @136
    @132
    cc0
    @63
    @136
    @16
    cN
    wceq
    #
    @131
    @63
    @16
    cN
    @75
    @119
    subeq0ad
    vm
    cN
    velsn
    syl6rbbr
    ifbid
    @63
    @126
    @18
    @22
    @137
    cmul
    co
    #
    vc
    csu
    @138
    @63
    @18
    @125
    @141
    vc
    @73
    @124
    @137
    @22
    cmul
    @73
    @23
    cz
    wcel
    @124
    @137
    wceq
    @73
    @16
    cN
    @76
    wph
    cN
    cz
    wcel
    #
    @58
    @67
    wph
    cN
    circlemeth.n
    nn0zd
    #
    ad2antrr
    zsubcld
    vx
    @23
    itgexpif
    syl
    oveq2d
    sumeq2dv
    @63
    @18
    @22
    @137
    vc
    @106
    @63
    @136
    c1
    cc0
    cc
    @63
    1cnd
    @63
    0cnd
    ifcld
    @111
    fsummulc1
    eqtr4d
    3eqtr4rd
    sumeq2dv
    wph
    @130
    @14
    wss
    @132
    cc
    wcel
    #
    vm
    @130
    wral
    @14
    cc0
    cuz
    cfv
    wss
    #
    @14
    cfn
    wcel
    #
    wo
    @135
    @134
    wceq
    wph
    cN
    @14
    wph
    cc0
    cz
    wcel
    @13
    cz
    wcel
    @142
    cc0
    cN
    cle
    wbr
    cN
    @13
    cle
    wbr
    #
    cN
    @14
    wcel
    wph
    0zd
    wph
    cS
    cN
    wph
    cS
    @47
    nn0zd
    @143
    zmulcld
    @143
    wph
    cN
    circlemeth.n
    nn0ge0d
    wph
    cS
    cn
    wcel
    @44
    @147
    circlemeth.s
    circlemeth.n
    cS
    cN
    nnmulge
    syl2anc
    cN
    cc0
    @13
    elfz4
    syl32anc
    snssd
    #
    wph
    @144
    vm
    @130
    wph
    @131
    @58
    @144
    wph
    @130
    @14
    @16
    @148
    sselda
    @139
    syldan
    ralrimiva
    wph
    @146
    @145
    @101
    olcd
    @130
    @14
    @132
    vm
    cc0
    sumss2
    syl21anc
    wph
    @44
    @129
    cc
    wcel
    @135
    @129
    wceq
    circlemeth.n
    wph
    @128
    @22
    vc
    wph
    @15
    cS
    cN
    @60
    wph
    @61
    a1i
    @143
    @47
    wph
    c1
    cN
    fzfid
    reprfi
    wph
    @19
    @128
    wcel
    #
    wa
    #
    @1
    @21
    va
    @69
    @150
    @70
    a1i
    @150
    @71
    wa
    #
    cS
    cL
    cN
    @3
    @20
    cN
    wph
    @44
    @149
    @71
    circlemeth.n
    ad2antrr
    wph
    @46
    @149
    @71
    @47
    ad2antrr
    wph
    @96
    @149
    @71
    @53
    ad2antrr
    wph
    @49
    @149
    @71
    circlemeth.l
    ad2antrr
    @150
    @71
    simpr
    @151
    @15
    cn
    @20
    @61
    @150
    @1
    @15
    @3
    @19
    @150
    @15
    @19
    cS
    cN
    @60
    @150
    @61
    a1i
    wph
    @142
    @149
    @143
    adantr
    wph
    @46
    @149
    @47
    adantr
    wph
    @149
    simpr
    reprf
    ffvelrnda
    sseldi
    breprexplemb
    fprodcl
    fsumcl
    @132
    @129
    vm
    cN
    cn0
    @140
    @18
    @128
    @22
    vc
    @16
    cN
    @15
    @17
    oveq2
    sumeq1d
    sumsn
    syl2anc
    3eqtr2d
    wph
    @14
    @31
    @126
    vm
    @63
    @31
    @104
    @126
    @63
    @102
    @105
    @123
    simprd
    @63
    @18
    @125
    @103
    vc
    @73
    vx
    @0
    @26
    @22
    cc
    @111
    @63
    @35
    @67
    @26
    cc
    wcel
    @110
    an32s
    @122
    itgmulc2
    sumeq2dv
    eqtr4d
    sumeq2dv
    wph
    @33
    @128
    @22
    vc
    wph
    cS
    cN
    circlemeth.n
    @47
    reprfz1
    sumeq1d
    3eqtr4d
    3eqtrrd
end
