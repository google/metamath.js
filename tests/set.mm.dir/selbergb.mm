include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "clog.mm"
include "cdiv.mm"
include "cchp.mm"
include "caddc.mm"
include "cmul.mm"
include "csu.mm"
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
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "adantr.mm"
include "nndivred.mm"
include "chpcl.mm"
include "readdcld.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "1rp.mm"
include "simplbda.mm"
include "rpgecld.mm"
include "rerpdivcld.mm"
include "2re.mm"
include "resubcld.mm"
include "recnd.mm"
include "cmpt.mm"
include "co1.mm"
include "selberg.mm"
include "o1res2.mm"
include "simprl.mm"
include "simprr.mm"
include "clt.mm"
include "abscld.mm"
include "simprll.mm"
include "ltled.mm"
include "abs2dif2d.mm"
include "cc0.mm"
include "vmage0.mm"
include "nnred.mm"
include "nnge1d.mm"
include "logge0d.mm"
include "chpge0.mm"
include "addge0d.mm"
include "mulge0d.mm"
include "fsumge0.mm"
include "divge0d.mm"
include "absidd.mm"
include "2rp.mm"
include "rpge0.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "flword2.mm"
include "syl3anc.mm"
include "fzss2.mm"
include "fsumless.mm"
include "lediv1dd.mm"
include "chpwordi.mm"
include "leadd2dd.mm"
include "lemul2ad.mm"
include "fsumle.mm"
include "letrd.mm"
include "lediv12ad.mm"
include "div1d.mm"
include "logled.mm"
include "mpbid.mm"
include "le2addd.mm"
include "o1bddrp.mm"
include "trud.mm"

theorem selbergb
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
  assert |- E. c e. RR+ A. x e. ( 1 [,) +oo ) ( abs ` ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. ( ( log ` n ) + ( psi ` ( x / n ) ) ) ) / x ) - ( 2 x. ( log ` x ) ) ) ) <_ c

  proof
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
    @3
    clog
    cfv
    #
    @0
    @3
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @0
    cdiv
    co
    #
    c2
    @0
    clog
    cfv
    #
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
    @16
    @14
    c1
    vc
    c1
    vy
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @4
    @5
    @17
    @3
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    c2
    @17
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wtru
    vx
    @16
    cr
    wtru
    @0
    @16
    wcel
    #
    @0
    cr
    wcel
    #
    wtru
    @28
    @29
    c1
    @0
    cle
    wbr
    #
    c1
    cr
    wcel
    #
    @28
    @29
    @30
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
    @31
    wtru
    1re
    a1i
    wtru
    @28
    wa
    #
    @14
    @34
    @11
    @13
    @34
    @10
    @0
    @34
    @2
    @9
    vn
    @34
    c1
    @1
    fzfid
    #
    @34
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @8
    @37
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    #
    @36
    @38
    @34
    @3
    @1
    elfznn
    adantl
    #
    @3
    vmacl
    #
    syl
    #
    @37
    @5
    @7
    @37
    @3
    @37
    @3
    @40
    nnrpd
    relogcld
    #
    @37
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @37
    @0
    @3
    @34
    @29
    @36
    @33
    adantr
    @40
    nndivred
    #
    @6
    chpcl
    #
    syl
    #
    readdcld
    #
    remulcld
    #
    fsumrecl
    #
    @34
    @0
    c1
    @33
    c1
    crp
    wcel
    #
    @34
    1rp
    a1i
    wtru
    @28
    @29
    @30
    @32
    simplbda
    #
    rpgecld
    #
    rerpdivcld
    #
    @34
    c2
    @12
    c2
    cr
    wcel
    #
    @34
    2re
    a1i
    @34
    @0
    @54
    relogcld
    remulcld
    #
    resubcld
    #
    recnd
    wtru
    vx
    @16
    crp
    @14
    wtru
    vx
    @16
    crp
    wtru
    @28
    @0
    crp
    wcel
    #
    @54
    ex
    ssrdv
    vx
    crp
    @14
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    selberg
    a1i
    o1res2
    wtru
    @17
    cr
    wcel
    #
    c1
    @17
    cle
    wbr
    #
    wa
    #
    wa
    #
    @24
    @26
    @63
    @19
    @23
    vn
    @63
    c1
    @18
    fzfid
    @63
    @3
    @19
    wcel
    #
    wa
    #
    @4
    @22
    @65
    @38
    @39
    @64
    @38
    @63
    @3
    @18
    elfznn
    #
    adantl
    #
    @41
    syl
    @65
    @5
    @21
    @65
    @3
    @65
    @3
    @67
    nnrpd
    relogcld
    @65
    @20
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @65
    @17
    @3
    @63
    @60
    @64
    wtru
    @60
    @61
    simprl
    #
    adantr
    @67
    nndivred
    @20
    chpcl
    #
    syl
    readdcld
    remulcld
    fsumrecl
    @63
    c2
    @25
    @56
    @63
    2re
    a1i
    @63
    @17
    @63
    @17
    c1
    @70
    @52
    @63
    1rp
    a1i
    wtru
    @60
    @61
    simprr
    rpgecld
    relogcld
    remulcld
    readdcld
    @34
    @62
    @0
    @17
    clt
    wbr
    #
    wa
    #
    wa
    #
    @15
    @11
    @13
    caddc
    co
    #
    @27
    @74
    @14
    @74
    @14
    @34
    @14
    cr
    wcel
    @73
    @58
    adantr
    recnd
    abscld
    @74
    @11
    @13
    @34
    @11
    cr
    wcel
    @73
    @55
    adantr
    #
    @34
    @13
    cr
    wcel
    @73
    @57
    adantr
    #
    readdcld
    @74
    @24
    @26
    @74
    @19
    @23
    vn
    @74
    c1
    @18
    fzfid
    #
    @74
    @64
    wa
    #
    @4
    @22
    @79
    @38
    @39
    @64
    @38
    @74
    @66
    adantl
    #
    @41
    syl
    #
    @79
    @5
    @21
    @79
    @3
    @79
    @3
    @80
    nnrpd
    #
    relogcld
    #
    @79
    @68
    @69
    @79
    @17
    @3
    @74
    @60
    @64
    @34
    @60
    @61
    @72
    simprll
    #
    adantr
    #
    @80
    nndivred
    #
    @71
    syl
    #
    readdcld
    #
    remulcld
    #
    fsumrecl
    #
    @74
    c2
    @25
    @56
    @74
    2re
    a1i
    #
    @74
    @17
    @74
    @17
    @0
    @84
    @34
    @59
    @73
    @54
    adantr
    #
    @74
    @0
    @17
    @34
    @29
    @73
    @33
    adantr
    #
    @84
    @34
    @62
    @72
    simprr
    ltled
    #
    rpgecld
    #
    relogcld
    #
    remulcld
    #
    readdcld
    @74
    @15
    @11
    cabs
    cfv
    #
    @13
    cabs
    cfv
    #
    caddc
    co
    @75
    cle
    @74
    @11
    @13
    @74
    @11
    @76
    recnd
    @74
    @13
    @77
    recnd
    abs2dif2d
    @74
    @98
    @11
    @99
    @13
    caddc
    @74
    @11
    @76
    @74
    @10
    @0
    @34
    @10
    cr
    wcel
    @73
    @51
    adantr
    #
    @92
    @34
    cc0
    @10
    cle
    wbr
    @73
    @34
    @2
    @9
    vn
    @35
    @50
    @37
    @4
    @8
    @42
    @49
    @37
    @38
    cc0
    @4
    cle
    wbr
    #
    @40
    @3
    vmage0
    #
    syl
    @37
    @5
    @7
    @43
    @48
    @37
    @3
    @37
    @3
    @40
    nnred
    @37
    @3
    @40
    nnge1d
    logge0d
    @37
    @44
    cc0
    @7
    cle
    wbr
    #
    @46
    @6
    chpge0
    #
    syl
    addge0d
    mulge0d
    fsumge0
    adantr
    #
    divge0d
    absidd
    @74
    @13
    @77
    @74
    c2
    @12
    @91
    @74
    @0
    @92
    relogcld
    #
    c2
    crp
    wcel
    cc0
    c2
    cle
    wbr
    @74
    2rp
    c2
    rpge0
    mp1i
    #
    @74
    @0
    @93
    @34
    @30
    @73
    @53
    adantr
    #
    logge0d
    mulge0d
    absidd
    oveq12d
    breqtrd
    @74
    @11
    @13
    @24
    @26
    @76
    @77
    @90
    @97
    @74
    @11
    @24
    c1
    cdiv
    co
    @24
    cle
    @74
    @10
    @24
    c1
    @0
    @100
    @90
    @52
    @74
    1rp
    a1i
    @93
    @105
    @74
    @10
    @19
    @9
    vn
    csu
    @24
    @100
    @74
    @19
    @9
    vn
    @78
    @79
    @4
    @8
    @81
    @79
    @5
    @7
    @83
    @79
    @44
    @45
    @79
    @0
    @3
    @74
    @29
    @64
    @93
    adantr
    #
    @80
    nndivred
    #
    @47
    syl
    #
    readdcld
    #
    remulcld
    #
    fsumrecl
    @90
    @74
    @19
    @9
    @2
    vn
    @78
    @113
    @79
    @4
    @8
    @81
    @112
    @79
    @38
    @101
    @80
    @102
    syl
    #
    @79
    @5
    @7
    @83
    @111
    @79
    @3
    @79
    @3
    @80
    nnred
    @79
    @3
    @80
    nnge1d
    logge0d
    @79
    @44
    @103
    @110
    @104
    syl
    addge0d
    mulge0d
    @74
    @18
    @1
    cuz
    cfv
    wcel
    #
    @2
    @19
    wss
    @74
    @29
    @60
    @0
    @17
    cle
    wbr
    #
    @115
    @93
    @84
    @94
    @0
    @17
    flword2
    syl3anc
    @1
    c1
    @18
    fzss2
    syl
    fsumless
    @74
    @19
    @9
    @23
    vn
    @78
    @113
    @89
    @79
    @8
    @22
    @4
    @112
    @88
    @81
    @114
    @79
    @7
    @21
    @5
    @111
    @87
    @83
    @79
    @44
    @68
    @6
    @20
    cle
    wbr
    @7
    @21
    cle
    wbr
    @110
    @86
    @79
    @0
    @17
    @3
    @109
    @85
    @82
    @74
    @116
    @64
    @94
    adantr
    lediv1dd
    @6
    @20
    chpwordi
    syl3anc
    leadd2dd
    lemul2ad
    fsumle
    letrd
    @108
    lediv12ad
    @74
    @24
    @74
    @24
    @90
    recnd
    div1d
    breqtrd
    @74
    @12
    @25
    c2
    @106
    @96
    @91
    @107
    @74
    @116
    @12
    @25
    cle
    wbr
    @94
    @74
    @0
    @17
    @92
    @95
    logled
    mpbid
    lemul2ad
    le2addd
    letrd
    o1bddrp
    trud
end
