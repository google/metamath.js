include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "clog.mm"
include "cmul.mm"
include "csu.mm"
include "cchp.mm"
include "cmin.mm"
include "cdiv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cioo.mm"
include "c2.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "caddc.mm"
include "cr.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "1re.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "simplbi.mm"
include "ssriv.mm"
include "a1i.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "chpcl.mm"
include "1rp.mm"
include "simprbi.mm"
include "rpgecld.mm"
include "resubcld.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "ex.mm"
include "ssrdv.mm"
include "selberg2lem.mm"
include "o1res2.mm"
include "ad2antrl.mm"
include "simprl.mm"
include "simprr.mm"
include "readdcld.mm"
include "clt.mm"
include "adantr.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "absdivd.mm"
include "rpge0d.mm"
include "absidd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "abscld.mm"
include "ad2ant2r.mm"
include "simprll.mm"
include "ltled.mm"
include "absge0d.mm"
include "lediv2ad.mm"
include "div1d.mm"
include "breqtrd.mm"
include "abs2dif2d.mm"
include "cc0.mm"
include "vmage0.mm"
include "nnred.mm"
include "nnge1d.mm"
include "logge0d.mm"
include "mulge0d.mm"
include "fsumge0.mm"
include "chpge0.mm"
include "oveq12d.mm"
include "cuz.mm"
include "flword2.mm"
include "syl3anc.mm"
include "fzss2.mm"
include "fsumless.mm"
include "chpwordi.mm"
include "logled.mm"
include "mpbid.mm"
include "lemul12ad.mm"
include "le2addd.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "o1bddrp.mm"
include "trud.mm"
include "simpl.mm"
include "simpr.mm"
include "selberg3lem1.mm"
include "rexlimiva.mm"

theorem selberg3lem2
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vm: setvar m
  let vy: setvar y

  disjoint n x
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) x. ( psi ` ( x / n ) ) ) x. ( log ` n ) ) ) - sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. ( psi ` ( x / n ) ) ) ) / x ) ) e. O(1)

  proof
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
    vm
    cv
    #
    cvma
    cfv
    #
    @3
    clog
    cfv
    #
    cmul
    co
    #
    vm
    csu
    #
    @0
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
    cmin
    co
    #
    @0
    cdiv
    co
    #
    cabs
    cfv
    #
    vc
    cv
    #
    cle
    wbr
    vy
    c1
    cpnf
    cico
    co
    #
    wral
    #
    vc
    crp
    wrex
    #
    vx
    c1
    cpnf
    cioo
    co
    c2
    vx
    cv
    #
    clog
    cfv
    #
    cdiv
    co
    c1
    @18
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
    @18
    @22
    cdiv
    co
    cchp
    cfv
    cmul
    co
    #
    @22
    clog
    cfv
    cmul
    co
    vn
    csu
    cmul
    co
    @21
    @23
    vn
    csu
    cmin
    co
    @18
    cdiv
    co
    cmpt
    co1
    wcel
    #
    @17
    wtru
    vy
    vx
    @15
    @12
    c1
    vc
    @21
    @6
    vm
    csu
    #
    @18
    cchp
    cfv
    #
    @19
    cmul
    co
    #
    caddc
    co
    #
    @15
    cr
    wss
    wtru
    vy
    @15
    cr
    @0
    @15
    wcel
    #
    @0
    cr
    wcel
    #
    c1
    @0
    cle
    wbr
    #
    c1
    cr
    wcel
    #
    @29
    @30
    @31
    wa
    wb
    1re
    c1
    @0
    elicopnf
    ax-mp
    #
    simplbi
    #
    ssriv
    a1i
    @32
    wtru
    1re
    a1i
    wtru
    @29
    wa
    #
    @12
    @35
    @11
    @0
    @35
    @7
    @10
    @35
    @2
    @6
    vm
    @35
    c1
    @1
    fzfid
    #
    @35
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @5
    @38
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    #
    @37
    @39
    @35
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
    @38
    @3
    @38
    @3
    @41
    nnrpd
    relogcld
    #
    remulcld
    #
    fsumrecl
    #
    @35
    @8
    @9
    @35
    @30
    @8
    cr
    wcel
    #
    @29
    @30
    wtru
    @34
    adantl
    #
    @0
    chpcl
    #
    syl
    @35
    @0
    @35
    @0
    c1
    @48
    c1
    crp
    wcel
    #
    @35
    1rp
    a1i
    @29
    @31
    wtru
    @29
    @30
    @31
    @33
    simprbi
    adantl
    #
    rpgecld
    #
    relogcld
    remulcld
    #
    resubcld
    #
    @52
    rerpdivcld
    recnd
    wtru
    vy
    @15
    crp
    @12
    wtru
    vy
    @15
    crp
    wtru
    @29
    @0
    crp
    wcel
    #
    @52
    ex
    ssrdv
    vy
    crp
    @12
    cmpt
    co1
    wcel
    wtru
    vy
    vm
    selberg2lem
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
    @25
    @27
    @59
    @21
    @6
    vm
    @59
    c1
    @20
    fzfid
    @59
    @3
    @21
    wcel
    #
    wa
    #
    @4
    @5
    @61
    @39
    @40
    @60
    @39
    @59
    @3
    @20
    elfznn
    #
    adantl
    #
    @42
    syl
    @61
    @3
    @61
    @3
    @63
    nnrpd
    relogcld
    remulcld
    fsumrecl
    #
    @59
    @26
    @19
    @56
    @26
    cr
    wcel
    #
    wtru
    @57
    @18
    chpcl
    #
    ad2antrl
    @59
    @18
    @59
    @18
    c1
    wtru
    @56
    @57
    simprl
    @50
    @59
    1rp
    a1i
    wtru
    @56
    @57
    simprr
    rpgecld
    relogcld
    remulcld
    readdcld
    @35
    @58
    @0
    @18
    clt
    wbr
    #
    wa
    #
    wa
    #
    @13
    @11
    cabs
    cfv
    #
    @0
    cdiv
    co
    #
    @28
    cle
    @69
    @13
    @70
    @0
    cabs
    cfv
    #
    cdiv
    co
    @71
    @69
    @11
    @0
    @69
    @11
    @35
    @11
    cr
    wcel
    @68
    @54
    adantr
    recnd
    #
    @69
    @0
    @35
    @55
    @68
    @52
    adantr
    #
    rpcnd
    @69
    @0
    @74
    rpne0d
    absdivd
    @69
    @72
    @0
    @70
    cdiv
    @69
    @0
    @35
    @30
    @68
    @48
    adantr
    #
    @69
    @0
    @74
    rpge0d
    absidd
    oveq2d
    eqtrd
    @69
    @71
    @70
    @28
    @69
    @70
    @0
    @69
    @11
    @73
    abscld
    #
    @74
    rerpdivcld
    @76
    @69
    @25
    @27
    wtru
    @58
    @25
    cr
    wcel
    @29
    @67
    @64
    ad2ant2r
    #
    @69
    @26
    @19
    @69
    @56
    @65
    @35
    @56
    @57
    @67
    simprll
    #
    @66
    syl
    #
    @69
    @18
    @69
    @18
    @0
    @78
    @74
    @69
    @0
    @18
    @75
    @78
    @35
    @58
    @67
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
    #
    @69
    @71
    @70
    c1
    cdiv
    co
    @70
    cle
    @69
    c1
    @0
    @70
    @50
    @69
    1rp
    a1i
    @74
    @76
    @69
    @11
    @73
    absge0d
    @35
    @31
    @68
    @51
    adantr
    #
    lediv2ad
    @69
    @70
    @69
    @70
    @76
    recnd
    div1d
    breqtrd
    @69
    @70
    @7
    @10
    caddc
    co
    #
    @28
    @76
    @69
    @7
    @10
    @35
    @7
    cr
    wcel
    @68
    @46
    adantr
    #
    @69
    @8
    @9
    @69
    @30
    @47
    @75
    @49
    syl
    #
    @69
    @0
    @74
    relogcld
    #
    remulcld
    #
    readdcld
    @84
    @69
    @70
    @7
    cabs
    cfv
    #
    @10
    cabs
    cfv
    #
    caddc
    co
    @86
    cle
    @69
    @7
    @10
    @69
    @7
    @87
    recnd
    @69
    @10
    @35
    @10
    cr
    wcel
    @68
    @53
    adantr
    #
    recnd
    abs2dif2d
    @69
    @91
    @7
    @92
    @10
    caddc
    @69
    @7
    @87
    @35
    cc0
    @7
    cle
    wbr
    @68
    @35
    @2
    @6
    vm
    @36
    @45
    @38
    @4
    @5
    @43
    @44
    @38
    @39
    cc0
    @4
    cle
    wbr
    #
    @41
    @3
    vmage0
    #
    syl
    @38
    @3
    @38
    @3
    @41
    nnred
    @38
    @3
    @41
    nnge1d
    logge0d
    mulge0d
    fsumge0
    adantr
    absidd
    @69
    @10
    @93
    @69
    @8
    @9
    @88
    @89
    @69
    @30
    cc0
    @8
    cle
    wbr
    @75
    @0
    chpge0
    syl
    #
    @69
    @0
    @75
    @85
    logge0d
    #
    mulge0d
    absidd
    oveq12d
    breqtrd
    @69
    @7
    @10
    @25
    @27
    @87
    @90
    @77
    @83
    @69
    @21
    @6
    @2
    vm
    @69
    c1
    @20
    fzfid
    @69
    @60
    wa
    #
    @4
    @5
    @98
    @39
    @40
    @60
    @39
    @69
    @62
    adantl
    #
    @42
    syl
    #
    @98
    @3
    @98
    @3
    @99
    nnrpd
    relogcld
    #
    remulcld
    @98
    @4
    @5
    @100
    @101
    @98
    @39
    @94
    @99
    @95
    syl
    @98
    @3
    @98
    @3
    @99
    nnred
    @98
    @3
    @99
    nnge1d
    logge0d
    mulge0d
    @69
    @20
    @1
    cuz
    cfv
    wcel
    #
    @2
    @21
    wss
    @69
    @30
    @56
    @0
    @18
    cle
    wbr
    #
    @102
    @75
    @78
    @80
    @0
    @18
    flword2
    syl3anc
    @1
    c1
    @20
    fzss2
    syl
    fsumless
    @69
    @8
    @26
    @9
    @19
    @88
    @79
    @89
    @82
    @96
    @97
    @69
    @30
    @56
    @103
    @8
    @26
    cle
    wbr
    @75
    @78
    @80
    @0
    @18
    chpwordi
    syl3anc
    @69
    @103
    @9
    @19
    cle
    wbr
    @80
    @69
    @0
    @18
    @74
    @81
    logled
    mpbid
    lemul12ad
    le2addd
    letrd
    letrd
    eqbrtrd
    o1bddrp
    trud
    @16
    @24
    vc
    crp
    @14
    crp
    wcel
    #
    @16
    wa
    vx
    vy
    @14
    vm
    vn
    @104
    @16
    simpl
    @104
    @16
    simpr
    selberg3lem1
    rexlimiva
    ax-mp
end
