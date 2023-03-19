include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "cvma.mm"
include "cdiv.mm"
include "clog.mm"
include "cmul.mm"
include "csu.mm"
include "c2.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "cexp.mm"
include "wa.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "cr.mm"
include "elioore.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "rplogcld.mm"
include "rpne0d.mm"
include "divsubdird.mm"
include "resubcld.mm"
include "divrecd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divdiv32d.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"
include "mpteq2dva.mm"
include "rprecred.mm"
include "ex.mm"
include "ssrdv.mm"
include "crli.mm"
include "cdm.mm"
include "wf.mm"
include "ceu.mm"
include "cle.mm"
include "w3a.mm"
include "cabs.mm"
include "wi.mm"
include "eqid.mm"
include "logdivsum.mm"
include "simp2i.mm"
include "rlimdmo1.mm"
include "mp1i.mm"
include "o1res2.mm"
include "divlogrlim.mm"
include "rlimo1.mm"
include "o1mul2.mm"
include "eqeltrd.mm"
include "divcld.mm"
include "halfcld.mm"
include "subcld.mm"
include "vmacl.mm"
include "syl.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "remulcld.mm"
include "rpcnd.mm"
include "nnncan2d.mm"
include "nnmulcld.mm"
include "fsumsub.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "nnrecred.mm"
include "subdid.mm"
include "cc.mm"
include "divdiv1d.mm"
include "eqtr3d.mm"
include "sumeq2dv.mm"
include "reccld.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"
include "cdvds.mm"
include "crab.mm"
include "wceq.mm"
include "vmasum.mm"
include "cfn.mm"
include "wss.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ssrab2.mm"
include "simprr.mm"
include "sseldi.mm"
include "anassrs.mm"
include "fsumdivc.mm"
include "oveq2.mm"
include "ad2antrl.mm"
include "dvdsflsumcom.mm"
include "3eqtr4rd.mm"
include "3eqtr2d.mm"
include "clo1.mm"
include "rerpdivcld.mm"
include "ioossre.mm"
include "ax-1cn.mm"
include "o1const.mm"
include "mp2an.mm"
include "dividd.mm"
include "vmadivsum.mm"
include "o1dif.mm"
include "mpbird.mm"
include "o1lo1d.mm"
include "vmage0.mm"
include "divge0d.mm"
include "caddc.mm"
include "rpred.mm"
include "mulid2d.mm"
include "wb.mm"
include "fznnfl.mm"
include "simplbda.mm"
include "eqbrtrd.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "harmonicubnd.mm"
include "lesubadd2d.mm"
include "lemul2ad.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "fsumle.mm"
include "lediv1dd.mm"
include "adantrr.mm"
include "lo1le.mm"
include "0red.mm"
include "harmoniclbnd.mm"
include "subge0d.mm"
include "mulge0d.mm"
include "fsumge0.mm"
include "o1lo12.mm"
include "trud.mm"

theorem vmalogdivsum2
  let vx: setvar x
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z

  disjoint n x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) / n ) x. ( log ` ( x / n ) ) ) / ( log ` x ) ) - ( ( log ` x ) / 2 ) ) ) e. O(1)

  proof
    vx
    c1
    cpnf
    cioo
    co
    #
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @4
    cdiv
    co
    #
    @1
    @4
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    @1
    clog
    cfv
    #
    cdiv
    co
    #
    @11
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    co1
    wcel
    #
    wtru
    vx
    @0
    @3
    vk
    cv
    #
    clog
    cfv
    #
    @16
    cdiv
    co
    #
    vk
    csu
    #
    @11
    cdiv
    co
    #
    @13
    cmin
    co
    #
    cmpt
    #
    co1
    wcel
    @15
    wtru
    @22
    vx
    @0
    @19
    @11
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    c1
    @11
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @21
    @27
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @25
    @11
    cdiv
    co
    @20
    @24
    @11
    cdiv
    co
    #
    cmin
    co
    @27
    @21
    @29
    @19
    @24
    @11
    @29
    @19
    @29
    @3
    @18
    vk
    @29
    c1
    @2
    fzfid
    #
    @29
    @16
    @3
    wcel
    #
    wa
    #
    @17
    @16
    @33
    @16
    @33
    @16
    @32
    @16
    cn
    wcel
    #
    @29
    @16
    @2
    elfznn
    #
    adantl
    #
    nnrpd
    relogcld
    @36
    nndivred
    fsumrecl
    #
    recnd
    #
    @29
    @24
    @29
    @23
    @29
    @11
    @29
    @1
    @29
    @1
    c1
    @28
    @1
    cr
    wcel
    #
    wtru
    @1
    c1
    cpnf
    elioore
    adantl
    #
    c1
    crp
    wcel
    #
    @29
    1rp
    a1i
    #
    @29
    c1
    @1
    @29
    1red
    @40
    @29
    c1
    @1
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    @28
    @43
    @44
    wa
    wtru
    @1
    c1
    cpnf
    eliooord
    adantl
    simpld
    #
    ltled
    rpgecld
    #
    relogcld
    #
    resqcld
    #
    rehalfcld
    #
    recnd
    @29
    @11
    @47
    recnd
    #
    @29
    @11
    @29
    @1
    @40
    @45
    rplogcld
    #
    rpne0d
    #
    divsubdird
    @29
    @25
    @11
    @29
    @25
    @29
    @19
    @24
    @37
    @49
    resubcld
    #
    recnd
    @50
    @52
    divrecd
    @29
    @30
    @13
    @20
    cmin
    @29
    @30
    @23
    @11
    cdiv
    co
    #
    c2
    cdiv
    co
    @13
    @29
    @23
    c2
    @11
    @29
    @23
    @48
    recnd
    @29
    2cnd
    @50
    c2
    cc0
    wne
    @29
    2ne0
    a1i
    @52
    divdiv32d
    @29
    @54
    @11
    c2
    cdiv
    @29
    @54
    @11
    @11
    cmul
    co
    #
    @11
    cdiv
    co
    @11
    @29
    @23
    @55
    @11
    cdiv
    @29
    @11
    @50
    sqvald
    oveq1d
    @29
    @11
    @11
    @50
    @50
    @52
    divcan3d
    eqtrd
    oveq1d
    eqtrd
    oveq2d
    3eqtr3rd
    mpteq2dva
    wtru
    vx
    @0
    @25
    @26
    cr
    @53
    @29
    @11
    @51
    rprecred
    #
    wtru
    vx
    @0
    crp
    @25
    wtru
    vx
    @0
    crp
    wtru
    @28
    @1
    crp
    wcel
    #
    @46
    ex
    ssrdv
    #
    vx
    crp
    @25
    cmpt
    #
    crli
    cdm
    wcel
    #
    @59
    co1
    wcel
    wtru
    crp
    cr
    @59
    wf
    @60
    @59
    c1
    crli
    wbr
    @41
    ceu
    c1
    cle
    wbr
    w3a
    c1
    @59
    cfv
    c1
    cmin
    co
    cabs
    cfv
    c1
    clog
    cfv
    c1
    cdiv
    co
    cle
    wbr
    wi
    vx
    c1
    vk
    @59
    c1
    @59
    eqid
    logdivsum
    simp2i
    @59
    rlimdmo1
    mp1i
    o1res2
    vx
    @0
    @26
    cmpt
    #
    cc0
    crli
    wbr
    @61
    co1
    wcel
    wtru
    vx
    divlogrlim
    cc0
    @61
    rlimo1
    mp1i
    #
    o1mul2
    eqeltrd
    wtru
    vx
    @0
    @21
    @14
    @29
    @20
    @13
    @29
    @19
    @11
    @38
    @50
    @52
    divcld
    #
    @29
    @11
    @50
    halfcld
    #
    subcld
    @29
    @12
    @13
    @29
    @10
    @11
    @29
    @10
    @29
    @3
    @9
    vn
    @31
    @29
    @4
    @3
    wcel
    #
    wa
    #
    @6
    @8
    @66
    @5
    @4
    @66
    @4
    cn
    wcel
    #
    @5
    cr
    wcel
    #
    @65
    @67
    @29
    @4
    @2
    elfznn
    adantl
    #
    @4
    vmacl
    #
    syl
    #
    @69
    nndivred
    #
    @66
    @7
    @66
    @1
    @4
    @29
    @57
    @65
    @46
    adantr
    @66
    @4
    @69
    nnrpd
    #
    rpdivcld
    #
    relogcld
    #
    remulcld
    #
    fsumrecl
    recnd
    #
    @29
    @11
    @51
    rpcnd
    #
    @52
    divcld
    #
    @29
    @11
    @78
    halfcld
    subcld
    wtru
    vx
    @0
    @21
    @14
    cmin
    co
    #
    cmpt
    vx
    @0
    @3
    @6
    c1
    @7
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @8
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @11
    cdiv
    co
    #
    cmpt
    #
    co1
    wtru
    vx
    @0
    @80
    @89
    @29
    @80
    @20
    @12
    cmin
    co
    @19
    @10
    cmin
    co
    #
    @11
    cdiv
    co
    @89
    @29
    @20
    @12
    @13
    @63
    @79
    @64
    nnncan2d
    @29
    @19
    @10
    @11
    @38
    @77
    @50
    @52
    divsubdird
    @29
    @91
    @88
    @11
    cdiv
    @29
    @3
    @82
    @5
    @4
    @83
    cmul
    co
    #
    cdiv
    co
    #
    vm
    csu
    #
    @9
    cmin
    co
    #
    vn
    csu
    @3
    @94
    vn
    csu
    #
    @10
    cmin
    co
    @88
    @91
    @29
    @3
    @94
    @9
    vn
    @31
    @66
    @94
    @66
    @82
    @93
    vm
    @66
    c1
    @81
    fzfid
    #
    @66
    @83
    @82
    wcel
    #
    wa
    #
    @5
    @92
    @66
    @68
    @98
    @71
    adantr
    @99
    @4
    @83
    @66
    @67
    @98
    @69
    adantr
    @98
    @83
    cn
    wcel
    @66
    @83
    @81
    elfznn
    adantl
    #
    nnmulcld
    nndivred
    fsumrecl
    recnd
    @66
    @9
    @76
    recnd
    fsumsub
    @29
    @3
    @87
    @95
    vn
    @66
    @87
    @6
    @85
    cmul
    co
    #
    @9
    cmin
    co
    @95
    @66
    @6
    @85
    @8
    @66
    @5
    @4
    @66
    @5
    @71
    recnd
    #
    @66
    @4
    @69
    nncnd
    #
    @66
    @4
    @69
    nnne0d
    #
    divcld
    #
    @66
    @85
    @66
    @82
    @84
    vm
    @97
    @99
    @83
    @100
    nnrecred
    fsumrecl
    #
    recnd
    @66
    @8
    @75
    recnd
    subdid
    @66
    @94
    @101
    @9
    cmin
    @66
    @94
    @82
    @6
    @84
    cmul
    co
    #
    vm
    csu
    @101
    @66
    @82
    @93
    @107
    vm
    @99
    @6
    @83
    cdiv
    co
    @93
    @107
    @99
    @5
    @4
    @83
    @66
    @5
    cc
    wcel
    #
    @98
    @102
    adantr
    #
    @66
    @4
    cc
    wcel
    @98
    @103
    adantr
    #
    @99
    @83
    @100
    nncnd
    #
    @66
    @4
    cc0
    wne
    @98
    @104
    adantr
    #
    @99
    @83
    @100
    nnne0d
    #
    divdiv1d
    @99
    @6
    @83
    @99
    @5
    @4
    @109
    @110
    @112
    divcld
    @111
    @113
    divrecd
    eqtr3d
    sumeq2dv
    @66
    @82
    @84
    @6
    vm
    @97
    @105
    @99
    @83
    @111
    @113
    reccld
    fsummulc2
    eqtr4d
    oveq1d
    eqtr4d
    sumeq2dv
    @29
    @19
    @96
    @10
    cmin
    @29
    @19
    @3
    vy
    cv
    @16
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    @5
    @16
    cdiv
    co
    #
    vn
    csu
    #
    vk
    csu
    @96
    @29
    @3
    @18
    @117
    vk
    @33
    @115
    @5
    vn
    csu
    #
    @16
    cdiv
    co
    @18
    @117
    @33
    @118
    @17
    @16
    cdiv
    @33
    @34
    @118
    @17
    wceq
    @36
    vy
    @16
    vn
    vmasum
    syl
    oveq1d
    @33
    @115
    @5
    @16
    vn
    @33
    c1
    @16
    cfz
    co
    #
    cfn
    wcel
    @115
    @119
    wss
    #
    @115
    cfn
    wcel
    @33
    c1
    @16
    fzfid
    @33
    @34
    @120
    @36
    @16
    vy
    dvdsssfz1
    syl
    @119
    @115
    ssfi
    syl2anc
    @33
    @16
    @36
    nncnd
    @29
    @32
    @4
    @115
    wcel
    #
    @108
    @29
    @32
    @121
    wa
    wa
    #
    @5
    @122
    @67
    @68
    @122
    @115
    cn
    @4
    @114
    vy
    cn
    ssrab2
    @29
    @32
    @121
    simprr
    sseldi
    @70
    syl
    recnd
    #
    anassrs
    @33
    @16
    @36
    nnne0d
    fsumdivc
    eqtr3d
    sumeq2dv
    @29
    vy
    @1
    @116
    @93
    vm
    vk
    vn
    @16
    @92
    @5
    cdiv
    oveq2
    @40
    @122
    @5
    @16
    @123
    @122
    @16
    @32
    @34
    @29
    @121
    @35
    ad2antrl
    #
    nncnd
    @122
    @16
    @124
    nnne0d
    divcld
    dvdsflsumcom
    eqtrd
    oveq1d
    3eqtr4rd
    oveq1d
    3eqtr2d
    mpteq2dva
    wtru
    @90
    co1
    wcel
    @90
    clo1
    wcel
    wtru
    vx
    @0
    @3
    @6
    vn
    csu
    #
    @11
    cdiv
    co
    #
    @89
    c1
    cr
    wtru
    1red
    wtru
    vx
    @0
    @126
    @29
    @125
    @11
    @29
    @3
    @6
    vn
    @31
    @72
    fsumrecl
    #
    @51
    rerpdivcld
    #
    wtru
    vx
    @0
    @126
    cmpt
    co1
    wcel
    vx
    @0
    c1
    cmpt
    co1
    wcel
    #
    @129
    wtru
    @0
    cr
    wss
    c1
    cc
    wcel
    @129
    c1
    cpnf
    ioossre
    ax-1cn
    vx
    @0
    c1
    o1const
    mp2an
    a1i
    wtru
    vx
    @0
    @126
    c1
    @29
    @126
    @128
    recnd
    @29
    c1
    @42
    rpcnd
    wtru
    vx
    @0
    @126
    c1
    cmin
    co
    #
    cmpt
    vx
    @0
    @125
    @11
    cmin
    co
    #
    @26
    cmul
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @130
    @132
    @29
    @131
    @11
    cdiv
    co
    @126
    @11
    @11
    cdiv
    co
    #
    cmin
    co
    @132
    @130
    @29
    @125
    @11
    @11
    @29
    @125
    @127
    recnd
    #
    @50
    @50
    @52
    divsubdird
    @29
    @131
    @11
    @29
    @125
    @11
    @134
    @50
    subcld
    @50
    @52
    divrecd
    @29
    @133
    c1
    @126
    cmin
    @29
    @11
    @50
    @52
    dividd
    oveq2d
    3eqtr3rd
    mpteq2dva
    wtru
    vx
    @0
    @131
    @26
    cr
    @29
    @125
    @11
    @127
    @47
    resubcld
    @56
    wtru
    vx
    @0
    crp
    @131
    @58
    vx
    crp
    @131
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    vmadivsum
    a1i
    o1res2
    @62
    o1mul2
    eqeltrd
    o1dif
    mpbird
    o1lo1d
    @128
    @29
    @88
    @11
    @29
    @3
    @87
    vn
    @31
    @66
    @6
    @86
    @72
    @66
    @85
    @8
    @106
    @75
    resubcld
    #
    remulcld
    #
    fsumrecl
    #
    @51
    rerpdivcld
    #
    wtru
    @28
    @89
    @126
    cle
    wbr
    c1
    @1
    cle
    wbr
    @29
    @88
    @125
    @11
    @137
    @127
    @51
    @29
    @3
    @87
    @6
    vn
    @31
    @136
    @72
    @66
    @87
    @6
    c1
    cmul
    co
    @6
    cle
    @66
    @86
    c1
    @6
    @135
    @66
    1red
    #
    @72
    @66
    @5
    @4
    @71
    @73
    @66
    @67
    cc0
    @5
    cle
    wbr
    @69
    @4
    vmage0
    syl
    divge0d
    #
    @66
    @86
    c1
    cle
    wbr
    @85
    @8
    c1
    caddc
    co
    cle
    wbr
    #
    @66
    @7
    cr
    wcel
    c1
    @7
    cle
    wbr
    #
    @141
    @66
    @7
    @74
    rpred
    @66
    c1
    @4
    cmul
    co
    #
    @1
    cle
    wbr
    @142
    @66
    @143
    @4
    @1
    cle
    @66
    @4
    @103
    mulid2d
    @29
    @65
    @67
    @4
    @1
    cle
    wbr
    #
    @29
    @39
    @65
    @67
    @144
    wa
    wb
    @40
    @4
    @1
    fznnfl
    syl
    simplbda
    eqbrtrd
    @66
    c1
    @1
    @4
    @139
    @29
    @39
    @65
    @40
    adantr
    @73
    lemuldivd
    mpbid
    @7
    vm
    harmonicubnd
    syl2anc
    @66
    @85
    @8
    c1
    @106
    @75
    @139
    lesubadd2d
    mpbird
    lemul2ad
    @66
    @6
    @105
    mulid1d
    breqtrd
    fsumle
    lediv1dd
    adantrr
    lo1le
    wtru
    vx
    @0
    @89
    cc0
    @138
    wtru
    0red
    @29
    @88
    @11
    @137
    @51
    @29
    @3
    @87
    vn
    @31
    @136
    @66
    @6
    @86
    @72
    @135
    @140
    @66
    cc0
    @86
    cle
    wbr
    @8
    @85
    cle
    wbr
    #
    @66
    @7
    crp
    wcel
    @145
    @74
    @7
    vm
    harmoniclbnd
    syl
    @66
    @85
    @8
    @106
    @75
    subge0d
    mpbird
    mulge0d
    fsumge0
    divge0d
    o1lo12
    mpbird
    eqeltrd
    o1dif
    mpbid
    trud
end
