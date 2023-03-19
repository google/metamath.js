include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "clog.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "caddc.mm"
include "c2.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wtru.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "mp1i.mm"
include "simprbda.mm"
include "ex.mm"
include "ssrdv.mm"
include "a1i.mm"
include "chpcl.mm"
include "syl.mm"
include "1rp.mm"
include "simplbda.mm"
include "rpgecld.mm"
include "relogcld.mm"
include "remulcld.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "adantr.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "readdcld.mm"
include "rerpdivcld.mm"
include "2re.mm"
include "resubcld.mm"
include "recnd.mm"
include "cmpt.mm"
include "co1.mm"
include "selberg2.mm"
include "o1res2.mm"
include "ad2antrl.mm"
include "simprl.mm"
include "simprr.mm"
include "clt.mm"
include "abscld.mm"
include "ad2ant2r.mm"
include "abs2dif2d.mm"
include "simprll.mm"
include "ltled.mm"
include "cc0.mm"
include "chpge0.mm"
include "logge0d.mm"
include "mulge0d.mm"
include "vmage0.mm"
include "fsumge0.mm"
include "addge0d.mm"
include "divge0d.mm"
include "absidd.mm"
include "chpwordi.mm"
include "syl3anc.mm"
include "logled.mm"
include "mpbid.mm"
include "lemul12ad.mm"
include "cuz.mm"
include "wss.mm"
include "flword2.mm"
include "fzss2.mm"
include "fsumless.mm"
include "nnrpd.mm"
include "lediv1dd.mm"
include "lemul2ad.mm"
include "fsumle.mm"
include "letrd.mm"
include "le2addd.mm"
include "lediv12ad.mm"
include "div1d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "2rp.mm"
include "rpge0.mm"
include "o1bddrp.mm"
include "trud.mm"

theorem selberg2b
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y

  disjoint c n
  disjoint c x
  disjoint n x
  disjoint c d
  disjoint c m
  disjoint c y
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- E. c e. RR+ A. x e. ( 1 [,) +oo ) ( abs ` ( ( ( ( ( psi ` x ) x. ( log ` x ) ) + sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. ( psi ` ( x / n ) ) ) ) / x ) - ( 2 x. ( log ` x ) ) ) ) <_ c

  proof
    vx
    cv
    #
    cchp
    cfv
    #
    @0
    clog
    cfv
    #
    cmul
    co
    #
    c1
    @0
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
    @0
    @6
    cdiv
    co
    #
    cchp
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    caddc
    co
    #
    @0
    cdiv
    co
    #
    c2
    @2
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vc
    cv
    cle
    wbr
    vx
    c1
    cpnf
    cico
    co
    #
    wral
    vc
    crp
    wrex
    wtru
    vx
    vy
    @17
    @15
    c1
    vc
    vy
    cv
    #
    cchp
    cfv
    #
    @18
    clog
    cfv
    #
    cmul
    co
    #
    c1
    @18
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    @18
    @6
    cdiv
    co
    #
    cchp
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    caddc
    co
    #
    c2
    @20
    cmul
    co
    #
    caddc
    co
    #
    wtru
    vx
    @17
    cr
    wtru
    @0
    @17
    wcel
    #
    @0
    cr
    wcel
    #
    wtru
    @31
    @32
    c1
    @0
    cle
    wbr
    #
    c1
    cr
    wcel
    #
    @31
    @32
    @33
    wa
    wb
    wtru
    1re
    c1
    @0
    elicopnf
    mp1i
    #
    simprbda
    #
    ex
    ssrdv
    @34
    wtru
    1re
    a1i
    wtru
    @31
    wa
    #
    @15
    @37
    @13
    @14
    @37
    @12
    @0
    @37
    @3
    @11
    @37
    @1
    @2
    @37
    @32
    @1
    cr
    wcel
    #
    @36
    @0
    chpcl
    #
    syl
    @37
    @0
    @37
    @0
    c1
    @36
    c1
    crp
    wcel
    #
    @37
    1rp
    a1i
    wtru
    @31
    @32
    @33
    @35
    simplbda
    #
    rpgecld
    #
    relogcld
    #
    remulcld
    @37
    @5
    @10
    vn
    @37
    c1
    @4
    fzfid
    #
    @37
    @6
    @5
    wcel
    #
    wa
    #
    @7
    @9
    @46
    @6
    cn
    wcel
    #
    @7
    cr
    wcel
    #
    @45
    @47
    @37
    @6
    @4
    elfznn
    adantl
    #
    @6
    vmacl
    #
    syl
    #
    @46
    @8
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    @46
    @0
    @6
    @37
    @32
    @45
    @36
    adantr
    @49
    nndivred
    #
    @8
    chpcl
    #
    syl
    #
    remulcld
    #
    fsumrecl
    #
    readdcld
    @42
    rerpdivcld
    #
    @37
    c2
    @2
    c2
    cr
    wcel
    #
    @37
    2re
    a1i
    @43
    remulcld
    #
    resubcld
    #
    recnd
    wtru
    vx
    @17
    crp
    @15
    wtru
    vx
    @17
    crp
    wtru
    @31
    @0
    crp
    wcel
    #
    @42
    ex
    ssrdv
    vx
    crp
    @15
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    selberg2
    a1i
    o1res2
    wtru
    @18
    cr
    wcel
    #
    c1
    @18
    cle
    wbr
    #
    wa
    #
    wa
    #
    @28
    @29
    @67
    @21
    @27
    @67
    @19
    @20
    @64
    @19
    cr
    wcel
    #
    wtru
    @65
    @18
    chpcl
    #
    ad2antrl
    @67
    @18
    @67
    @18
    c1
    wtru
    @64
    @65
    simprl
    #
    @40
    @67
    1rp
    a1i
    wtru
    @64
    @65
    simprr
    rpgecld
    relogcld
    #
    remulcld
    @67
    @23
    @26
    vn
    @67
    c1
    @22
    fzfid
    @67
    @6
    @23
    wcel
    #
    wa
    #
    @7
    @25
    @73
    @47
    @48
    @72
    @47
    @67
    @6
    @22
    elfznn
    #
    adantl
    #
    @50
    syl
    @73
    @24
    cr
    wcel
    #
    @25
    cr
    wcel
    #
    @73
    @18
    @6
    @67
    @64
    @72
    @70
    adantr
    @75
    nndivred
    @24
    chpcl
    #
    syl
    remulcld
    fsumrecl
    #
    readdcld
    @67
    c2
    @20
    @60
    @67
    2re
    a1i
    @71
    remulcld
    readdcld
    #
    @37
    @66
    @0
    @18
    clt
    wbr
    #
    wa
    #
    wa
    #
    @16
    @13
    cabs
    cfv
    #
    @14
    cabs
    cfv
    #
    caddc
    co
    @30
    @83
    @15
    @83
    @15
    @37
    @15
    cr
    wcel
    @82
    @62
    adantr
    recnd
    abscld
    @83
    @84
    @85
    @83
    @13
    @83
    @13
    @37
    @13
    cr
    wcel
    @82
    @59
    adantr
    #
    recnd
    #
    abscld
    #
    @83
    @14
    @83
    @14
    @37
    @14
    cr
    wcel
    @82
    @61
    adantr
    #
    recnd
    #
    abscld
    #
    readdcld
    wtru
    @66
    @30
    cr
    wcel
    @31
    @81
    @80
    ad2ant2r
    @83
    @13
    @14
    @87
    @90
    abs2dif2d
    @83
    @84
    @85
    @28
    @29
    @88
    @91
    @83
    @21
    @27
    @83
    @19
    @20
    @83
    @64
    @68
    @37
    @64
    @65
    @81
    simprll
    #
    @69
    syl
    #
    @83
    @18
    @83
    @18
    @0
    @92
    @37
    @63
    @82
    @42
    adantr
    #
    @83
    @0
    @18
    @37
    @32
    @82
    @36
    adantr
    #
    @92
    @37
    @66
    @81
    simprr
    ltled
    #
    rpgecld
    #
    relogcld
    #
    remulcld
    #
    wtru
    @66
    @27
    cr
    wcel
    @31
    @81
    @79
    ad2ant2r
    #
    readdcld
    #
    @83
    c2
    @20
    @60
    @83
    2re
    a1i
    #
    @98
    remulcld
    @83
    @84
    @13
    @28
    cle
    @83
    @13
    @86
    @83
    @12
    @0
    @83
    @3
    @11
    @83
    @1
    @2
    @83
    @32
    @38
    @95
    @39
    syl
    #
    @83
    @0
    @94
    relogcld
    #
    remulcld
    #
    @37
    @11
    cr
    wcel
    @82
    @58
    adantr
    #
    readdcld
    #
    @94
    @83
    @3
    @11
    @105
    @106
    @83
    @1
    @2
    @103
    @104
    @83
    @32
    cc0
    @1
    cle
    wbr
    @95
    @0
    chpge0
    syl
    #
    @83
    @0
    @95
    @37
    @33
    @82
    @41
    adantr
    #
    logge0d
    #
    mulge0d
    @37
    cc0
    @11
    cle
    wbr
    @82
    @37
    @5
    @10
    vn
    @44
    @57
    @46
    @7
    @9
    @51
    @56
    @46
    @47
    cc0
    @7
    cle
    wbr
    #
    @49
    @6
    vmage0
    #
    syl
    @46
    @52
    cc0
    @9
    cle
    wbr
    #
    @54
    @8
    chpge0
    #
    syl
    mulge0d
    fsumge0
    adantr
    addge0d
    #
    divge0d
    absidd
    @83
    @13
    @28
    c1
    cdiv
    co
    @28
    cle
    @83
    @12
    @28
    c1
    @0
    @107
    @101
    @40
    @83
    1rp
    a1i
    @95
    @115
    @83
    @3
    @11
    @21
    @27
    @105
    @106
    @99
    @100
    @83
    @1
    @19
    @2
    @20
    @103
    @93
    @104
    @98
    @108
    @110
    @83
    @32
    @64
    @0
    @18
    cle
    wbr
    #
    @1
    @19
    cle
    wbr
    @95
    @92
    @96
    @0
    @18
    chpwordi
    syl3anc
    @83
    @116
    @2
    @20
    cle
    wbr
    @96
    @83
    @0
    @18
    @94
    @97
    logled
    mpbid
    #
    lemul12ad
    @83
    @11
    @23
    @10
    vn
    csu
    @27
    @106
    @83
    @23
    @10
    vn
    @83
    c1
    @22
    fzfid
    #
    @83
    @72
    wa
    #
    @7
    @9
    @119
    @47
    @48
    @72
    @47
    @83
    @74
    adantl
    #
    @50
    syl
    #
    @119
    @52
    @53
    @119
    @0
    @6
    @83
    @32
    @72
    @95
    adantr
    #
    @120
    nndivred
    #
    @55
    syl
    #
    remulcld
    #
    fsumrecl
    @100
    @83
    @23
    @10
    @5
    vn
    @118
    @125
    @119
    @7
    @9
    @121
    @124
    @119
    @47
    @111
    @120
    @112
    syl
    #
    @119
    @52
    @113
    @123
    @114
    syl
    mulge0d
    @83
    @22
    @4
    cuz
    cfv
    wcel
    #
    @5
    @23
    wss
    @83
    @32
    @64
    @116
    @127
    @95
    @92
    @96
    @0
    @18
    flword2
    syl3anc
    @4
    c1
    @22
    fzss2
    syl
    fsumless
    @83
    @23
    @10
    @26
    vn
    @118
    @125
    @119
    @7
    @25
    @121
    @119
    @76
    @77
    @119
    @18
    @6
    @83
    @64
    @72
    @92
    adantr
    #
    @120
    nndivred
    #
    @78
    syl
    #
    remulcld
    @119
    @9
    @25
    @7
    @124
    @130
    @121
    @126
    @119
    @52
    @76
    @8
    @24
    cle
    wbr
    @9
    @25
    cle
    wbr
    @123
    @129
    @119
    @0
    @18
    @6
    @122
    @128
    @119
    @6
    @120
    nnrpd
    @83
    @116
    @72
    @96
    adantr
    lediv1dd
    @8
    @24
    chpwordi
    syl3anc
    lemul2ad
    fsumle
    letrd
    le2addd
    @109
    lediv12ad
    @83
    @28
    @83
    @28
    @101
    recnd
    div1d
    breqtrd
    eqbrtrd
    @83
    @85
    @14
    @29
    cle
    @83
    @14
    @89
    @83
    c2
    @2
    @102
    @104
    c2
    crp
    wcel
    cc0
    c2
    cle
    wbr
    @83
    2rp
    c2
    rpge0
    mp1i
    #
    @110
    mulge0d
    absidd
    @83
    @2
    @20
    c2
    @104
    @98
    @102
    @131
    @117
    lemul2ad
    eqbrtrd
    le2addd
    letrd
    o1bddrp
    trud
end
