include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "cmul.mm"
include "cdiv.mm"
include "csu.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cn.mm"
include "pntrsumbnd.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "2rp.mm"
include "rpmulcl.mm"
include "mpan.mm"
include "adantr.mm"
include "cmin.mm"
include "nnz.mm"
include "adantl.mm"
include "peano2zm.mm"
include "syl.mm"
include "simplr.mm"
include "wceq.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wi.mm"
include "c0.mm"
include "cc0.mm"
include "ad2antrr.mm"
include "rpge0d.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "abs00bd.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "a1d.mm"
include "wne.mm"
include "cuz.mm"
include "fzn0.mm"
include "cr.mm"
include "fzfid.mm"
include "elfznn.mm"
include "simpr.mm"
include "nnrpd.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "peano2nnd.mm"
include "nnmulcld.mm"
include "nndivred.mm"
include "sylan2.mm"
include "fsumrecl.mm"
include "recnd.mm"
include "abscld.mm"
include "simplll.mm"
include "rpred.mm"
include "le2add.mm"
include "syl22anc.mm"
include "2timesd.mm"
include "breq2d.mm"
include "clt.mm"
include "cin.mm"
include "simpllr.mm"
include "nnred.mm"
include "ltm1d.mm"
include "fzdisj.mm"
include "cun.mm"
include "cc.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnzd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "peano2uzr.mm"
include "syl2anc.mm"
include "fzsplit2.mm"
include "oveq1d.mm"
include "uneq2d.mm"
include "eqtrd.mm"
include "fsumsplit.mm"
include "elfzuz.mm"
include "eluznn.mm"
include "syl2an.mm"
include "syldan.mm"
include "pncan2d.mm"
include "abs2dif2d.mm"
include "eqbrtrrd.mm"
include "readdcld.mm"
include "2re.mm"
include "a1i.mm"
include "remulcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbird.mm"
include "syld.mm"
include "ancomsd.mm"
include "sylan2b.mm"
include "pm2.61dane.mm"
include "an4s.mm"
include "expr.mm"
include "ralimdva.mm"
include "impancom.mm"
include "an32s.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem pntrsumbnd2
  let cR: class R
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let cA: class A
  let vb: setvar b
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a k
  disjoint a m
  disjoint a n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint R c
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint a d
  disjoint a x
  disjoint A a
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint k x
  disjoint A k
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint d y
  disjoint R d
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint x y
  disjoint R x
  disjoint R y
  assert |- E. c e. RR+ A. k e. NN A. m e. ZZ ( abs ` sum_ n e. ( k ... m ) ( ( R ` n ) / ( n x. ( n + 1 ) ) ) ) <_ c

  proof
    c1
    vm
    cv
    #
    cfz
    co
    #
    vn
    cv
    #
    cR
    cfv
    #
    @2
    @2
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    vn
    csu
    #
    cabs
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vm
    cz
    wral
    #
    vb
    crp
    wrex
    vk
    cv
    #
    @0
    cfz
    co
    #
    @6
    vn
    csu
    #
    cabs
    cfv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vm
    cz
    wral
    vk
    cn
    wral
    #
    vc
    crp
    wrex
    #
    cR
    vm
    vn
    va
    vb
    pntrval.r
    pntrsumbnd
    @11
    @19
    vb
    crp
    @9
    crp
    wcel
    #
    @11
    wa
    #
    c2
    @9
    cmul
    co
    #
    crp
    wcel
    #
    @15
    @22
    cle
    wbr
    #
    vm
    cz
    wral
    #
    vk
    cn
    wral
    #
    @19
    @20
    @23
    @11
    c2
    crp
    wcel
    @20
    @23
    2rp
    c2
    @9
    rpmulcl
    mpan
    #
    adantr
    @21
    @25
    vk
    cn
    @21
    @12
    cn
    wcel
    #
    wa
    #
    c1
    @12
    c1
    cmin
    co
    #
    cfz
    co
    #
    @6
    vn
    csu
    #
    cabs
    cfv
    #
    @9
    cle
    wbr
    #
    @25
    @29
    @30
    cz
    wcel
    #
    @11
    @34
    @29
    @12
    cz
    wcel
    #
    @35
    @28
    @36
    @21
    @12
    nnz
    adantl
    @12
    peano2zm
    #
    syl
    @20
    @11
    @28
    simplr
    @10
    @34
    vm
    @30
    cz
    @0
    @30
    wceq
    #
    @8
    @33
    @9
    cle
    @38
    @7
    @32
    cabs
    @38
    @1
    @31
    @6
    vn
    @0
    @30
    c1
    cfz
    oveq2
    sumeq1d
    fveq2d
    breq1d
    rspcv
    sylc
    @20
    @28
    @11
    @34
    @25
    wi
    @20
    @28
    wa
    #
    @34
    @11
    @25
    @39
    @34
    wa
    #
    @10
    @24
    vm
    cz
    @40
    @0
    cz
    wcel
    #
    @10
    @24
    @39
    @41
    @34
    @10
    @24
    @39
    @41
    wa
    #
    @34
    @10
    wa
    #
    @24
    @42
    @43
    @24
    wi
    #
    @13
    c0
    @42
    @13
    c0
    wceq
    #
    wa
    @24
    @43
    @42
    @45
    @24
    @42
    @24
    @45
    cc0
    @22
    cle
    wbr
    @42
    @22
    @20
    @23
    @28
    @41
    @27
    ad2antrr
    rpge0d
    @45
    @15
    cc0
    @22
    cle
    @45
    @14
    @45
    @14
    c0
    @6
    vn
    csu
    cc0
    @13
    c0
    @6
    vn
    sumeq1
    @6
    vn
    sum0
    syl6eq
    abs00bd
    breq1d
    syl5ibrcom
    imp
    a1d
    @13
    c0
    wne
    @42
    @0
    @12
    cuz
    cfv
    #
    wcel
    #
    @44
    @12
    @0
    fzn0
    @42
    @47
    wa
    #
    @10
    @34
    @24
    @48
    @10
    @34
    wa
    #
    @8
    @33
    caddc
    co
    #
    @9
    @9
    caddc
    co
    #
    cle
    wbr
    #
    @24
    @48
    @8
    cr
    wcel
    @33
    cr
    wcel
    @9
    cr
    wcel
    #
    @53
    @49
    @52
    wi
    @48
    @7
    @48
    @7
    @48
    @1
    @6
    vn
    @48
    c1
    @0
    fzfid
    #
    @2
    @1
    wcel
    #
    @48
    @2
    cn
    wcel
    #
    @6
    cr
    wcel
    #
    @2
    @0
    elfznn
    @48
    @56
    wa
    #
    @3
    @5
    @58
    @2
    crp
    wcel
    @3
    cr
    wcel
    @58
    @2
    @48
    @56
    simpr
    #
    nnrpd
    crp
    cr
    @2
    cR
    cR
    va
    pntrval.r
    pntrf
    ffvelrni
    syl
    @58
    @2
    @4
    @59
    @58
    @2
    @59
    peano2nnd
    nnmulcld
    nndivred
    #
    sylan2
    #
    fsumrecl
    recnd
    #
    abscld
    #
    @48
    @32
    @48
    @32
    @48
    @31
    @6
    vn
    @48
    c1
    @30
    fzfid
    @2
    @31
    wcel
    @48
    @56
    @57
    @2
    @30
    elfznn
    @60
    sylan2
    fsumrecl
    recnd
    #
    abscld
    #
    @48
    @9
    @20
    @28
    @41
    @47
    simplll
    rpred
    #
    @66
    @8
    @33
    @9
    @9
    le2add
    syl22anc
    @48
    @52
    @50
    @22
    cle
    wbr
    #
    @24
    @48
    @22
    @51
    @50
    cle
    @48
    @9
    @48
    @9
    @66
    recnd
    2timesd
    breq2d
    @48
    @15
    @50
    cle
    wbr
    #
    @67
    @24
    @48
    @7
    @32
    cmin
    co
    #
    cabs
    cfv
    @15
    @50
    cle
    @48
    @69
    @14
    cabs
    @48
    @69
    @32
    @14
    caddc
    co
    #
    @32
    cmin
    co
    @14
    @48
    @7
    @70
    @32
    cmin
    @48
    @31
    @13
    @6
    @1
    vn
    @48
    @30
    @12
    clt
    wbr
    @31
    @13
    cin
    c0
    wceq
    @48
    @12
    @48
    @12
    @20
    @28
    @41
    @47
    simpllr
    #
    nnred
    ltm1d
    c1
    @30
    @12
    @0
    fzdisj
    syl
    @48
    @1
    @31
    @30
    c1
    caddc
    co
    #
    @0
    cfz
    co
    #
    cun
    #
    @31
    @13
    cun
    @48
    @72
    c1
    cuz
    cfv
    #
    wcel
    @0
    @30
    cuz
    cfv
    wcel
    #
    @1
    @74
    wceq
    @48
    @72
    cn
    @75
    @48
    @72
    @12
    cn
    @48
    @12
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @72
    @12
    wceq
    #
    @48
    @12
    @71
    nncnd
    ax-1cn
    @12
    c1
    npcan
    #
    sylancl
    #
    @71
    eqeltrd
    nnuz
    syl6eleq
    @48
    @35
    @0
    @72
    cuz
    cfv
    #
    wcel
    #
    @76
    @48
    @36
    @35
    @48
    @12
    @71
    nnzd
    @37
    syl
    @42
    @83
    @47
    @42
    @82
    @46
    @0
    @42
    @72
    @12
    cuz
    @42
    @77
    @78
    @79
    @42
    @12
    @20
    @28
    @41
    simplr
    nncnd
    ax-1cn
    @80
    sylancl
    fveq2d
    eleq2d
    biimpar
    @30
    @0
    peano2uzr
    syl2anc
    @30
    c1
    @0
    fzsplit2
    syl2anc
    @48
    @73
    @13
    @31
    @48
    @72
    @12
    @0
    cfz
    @81
    oveq1d
    uneq2d
    eqtrd
    @54
    @48
    @55
    wa
    @6
    @61
    recnd
    fsumsplit
    oveq1d
    @48
    @32
    @14
    @64
    @48
    @14
    @48
    @13
    @6
    vn
    @48
    @12
    @0
    fzfid
    @48
    @2
    @13
    wcel
    #
    @56
    @57
    @48
    @28
    @2
    @46
    wcel
    @56
    @84
    @71
    @2
    @12
    @0
    elfzuz
    @2
    @12
    eluznn
    syl2an
    @60
    syldan
    fsumrecl
    recnd
    #
    pncan2d
    eqtrd
    fveq2d
    @48
    @7
    @32
    @62
    @64
    abs2dif2d
    eqbrtrrd
    @48
    @15
    cr
    wcel
    @50
    cr
    wcel
    @22
    cr
    wcel
    @68
    @67
    wa
    @24
    wi
    @48
    @14
    @85
    abscld
    @48
    @8
    @33
    @63
    @65
    readdcld
    @48
    c2
    @9
    c2
    cr
    wcel
    @48
    2re
    a1i
    @66
    remulcld
    @15
    @50
    @22
    letr
    syl3anc
    mpand
    sylbird
    syld
    ancomsd
    sylan2b
    pm2.61dane
    imp
    an4s
    expr
    ralimdva
    impancom
    an32s
    mpd
    ralrimiva
    @18
    @26
    vc
    @22
    crp
    @16
    @22
    wceq
    @17
    @24
    vk
    vm
    cn
    cz
    @16
    @22
    @15
    cle
    breq2
    2ralbidv
    rspcev
    syl2anc
    rexlimiva
    ax-mp
end
