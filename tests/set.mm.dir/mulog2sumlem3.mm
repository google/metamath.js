include "crp.mm"
include "c2.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cmu.mm"
include "cdiv.mm"
include "clog.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "fzfid.mm"
include "cn.mm"
include "cz.mm"
include "elfznn.mm"
include "adantl.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "nndivred.mm"
include "recnd.mm"
include "simpr.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "relogcld.mm"
include "sqcld.mm"
include "halfcld.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "cr.mm"
include "relogcl.mm"
include "subdid.mm"
include "fsummulc2.mm"
include "mul12d.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "subcld.mm"
include "wss.mm"
include "rpssre.mm"
include "o1const.mm"
include "mp2an.mm"
include "cem.mm"
include "caddc.mm"
include "emre.mm"
include "recni.mm"
include "mulcl.mm"
include "sylancr.mm"
include "crli.mm"
include "wbr.mm"
include "rlimcl.mm"
include "ad2antrr.mm"
include "addcld.mm"
include "sub32d.mm"
include "fsumsub.mm"
include "pncand.mm"
include "eqtr3d.mm"
include "cabs.mm"
include "ceu.mm"
include "eqid.mm"
include "mulog2sumlem2.mm"
include "adantr.mm"
include "fsummulc1.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "3eqtr2d.mm"
include "mulogsum.mm"
include "o1mul2.mm"
include "mudivsum.mm"
include "o1sub2.mm"
include "eqeltrrd.mm"

theorem mulog2sumlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cL: class L
  let vk: setvar k
  let vm: setvar m
  let cA: class A
  let cR: class R
  assume logdivsum.1: |- F = ( y e. RR+ |-> ( sum_ i e. ( 1 ... ( |_ ` y ) ) ( ( log ` i ) / i ) - ( ( ( log ` y ) ^ 2 ) / 2 ) ) )
  assume mulog2sumlem.1: |- ( ph -> F ~~>r L )

  disjoint i n
  disjoint i x
  disjoint i y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint F x
  disjoint L n
  disjoint L x
  disjoint n ph
  disjoint ph x
  disjoint i k
  disjoint i m
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint k ph
  disjoint m ph
  disjoint R n
  disjoint R x
  assert |- ( ph -> ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( mmu ` n ) / n ) x. ( ( log ` ( x / n ) ) ^ 2 ) ) - ( 2 x. ( log ` x ) ) ) ) e. O(1) )

  proof
    wph
    vx
    crp
    c2
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
    cmu
    cfv
    #
    @3
    cdiv
    co
    #
    @0
    @3
    cdiv
    co
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @0
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cmpt
    vx
    crp
    @2
    @5
    @8
    cmul
    co
    #
    vn
    csu
    #
    c2
    @12
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    co1
    wph
    vx
    crp
    @14
    @18
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @14
    c2
    @11
    cmul
    co
    #
    @17
    cmin
    co
    @18
    @20
    c2
    @11
    @12
    c2
    cc
    wcel
    #
    @20
    2cn
    a1i
    #
    @20
    @2
    @10
    vn
    @20
    c1
    @1
    fzfid
    #
    @20
    @3
    @2
    wcel
    #
    wa
    #
    @5
    @9
    @26
    @5
    @26
    @4
    @3
    @26
    @4
    @26
    @3
    cn
    wcel
    #
    @4
    cz
    wcel
    @25
    @27
    @20
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    mucl
    syl
    zred
    @29
    nndivred
    recnd
    #
    @26
    @8
    @26
    @7
    @26
    @7
    @26
    @6
    @20
    @19
    @3
    crp
    wcel
    @6
    crp
    wcel
    @25
    wph
    @19
    simpr
    @25
    @3
    @28
    nnrpd
    @0
    @3
    rpdivcl
    syl2an
    relogcld
    recnd
    #
    sqcld
    #
    halfcld
    #
    mulcld
    #
    fsumcl
    #
    @20
    @12
    @19
    @12
    cr
    wcel
    wph
    @0
    relogcl
    adantl
    recnd
    #
    subdid
    @20
    @21
    @16
    @17
    cmin
    @20
    @21
    @2
    c2
    @10
    cmul
    co
    #
    vn
    csu
    @16
    @20
    @2
    @10
    c2
    vn
    @24
    @23
    @34
    fsummulc2
    @20
    @2
    @37
    @15
    vn
    @26
    @37
    @5
    c2
    @9
    cmul
    co
    #
    cmul
    co
    @15
    @26
    c2
    @5
    @9
    @22
    @26
    2cn
    a1i
    #
    @30
    @33
    mul12d
    @26
    @38
    @8
    @5
    cmul
    @26
    @8
    c2
    @32
    @39
    c2
    cc0
    wne
    @26
    2ne0
    a1i
    divcan2d
    oveq2d
    eqtrd
    sumeq2dv
    eqtrd
    oveq1d
    eqtrd
    mpteq2dva
    wph
    vx
    crp
    c2
    @13
    cc
    @23
    @20
    @11
    @12
    @35
    @36
    subcld
    vx
    crp
    c2
    cmpt
    co1
    wcel
    #
    wph
    crp
    cr
    wss
    #
    @22
    @40
    rpssre
    2cn
    vx
    crp
    c2
    o1const
    mp2an
    a1i
    wph
    vx
    crp
    @2
    @5
    @9
    cem
    @7
    cmul
    co
    #
    cL
    cmin
    co
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
    @12
    cmin
    co
    #
    @2
    @5
    @43
    cmul
    co
    #
    vn
    csu
    #
    cmin
    co
    #
    cmpt
    vx
    crp
    @13
    cmpt
    co1
    wph
    vx
    crp
    @50
    @13
    @20
    @50
    @46
    @49
    cmin
    co
    #
    @12
    cmin
    co
    @13
    @20
    @46
    @12
    @49
    @20
    @2
    @45
    vn
    @24
    @26
    @5
    @44
    @30
    @26
    @9
    @43
    @33
    @26
    @42
    cL
    @26
    cem
    cc
    wcel
    #
    @7
    cc
    wcel
    @42
    cc
    wcel
    cem
    emre
    recni
    #
    @31
    cem
    @7
    mulcl
    sylancr
    #
    wph
    cL
    cc
    wcel
    #
    @19
    @25
    wph
    cF
    cL
    crli
    wbr
    @55
    mulog2sumlem.1
    cL
    cF
    rlimcl
    syl
    #
    ad2antrr
    #
    subcld
    #
    addcld
    #
    mulcld
    #
    fsumcl
    #
    @36
    @20
    @2
    @48
    vn
    @24
    @26
    @5
    @43
    @30
    @58
    mulcld
    #
    fsumcl
    #
    sub32d
    @20
    @51
    @11
    @12
    cmin
    @20
    @2
    @45
    @48
    cmin
    co
    #
    vn
    csu
    @51
    @11
    @20
    @2
    @45
    @48
    vn
    @24
    @60
    @62
    fsumsub
    @20
    @2
    @64
    @10
    vn
    @26
    @5
    @44
    @43
    cmin
    co
    #
    cmul
    co
    @64
    @10
    @26
    @5
    @44
    @43
    @30
    @59
    @58
    subdid
    @26
    @65
    @9
    @5
    cmul
    @26
    @9
    @43
    @33
    @58
    pncand
    oveq2d
    eqtr3d
    sumeq2dv
    eqtr3d
    oveq1d
    eqtrd
    mpteq2dva
    wph
    vx
    crp
    @47
    @49
    cc
    @20
    @46
    @12
    @61
    @36
    subcld
    @63
    wph
    vx
    vy
    c1
    c2
    cdiv
    co
    cem
    cL
    cabs
    cfv
    caddc
    co
    caddc
    co
    c1
    c2
    cfz
    co
    ceu
    vm
    cv
    #
    cdiv
    co
    clog
    cfv
    @66
    cdiv
    co
    vm
    csu
    caddc
    co
    #
    @44
    vi
    vm
    vn
    cF
    cL
    logdivsum.1
    mulog2sumlem.1
    @44
    eqid
    @67
    eqid
    mulog2sumlem2
    wph
    vx
    crp
    cem
    @2
    @5
    @7
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    @2
    @5
    vn
    csu
    #
    cL
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    vx
    crp
    @49
    cmpt
    co1
    wph
    vx
    crp
    @73
    @49
    @20
    @73
    @2
    cem
    @68
    cmul
    co
    #
    vn
    csu
    #
    @2
    @5
    cL
    cmul
    co
    #
    vn
    csu
    #
    cmin
    co
    @2
    @74
    @76
    cmin
    co
    #
    vn
    csu
    @49
    @20
    @70
    @75
    @72
    @77
    cmin
    @20
    @2
    @68
    cem
    vn
    @24
    @52
    @20
    @53
    a1i
    #
    @26
    @5
    @7
    @30
    @31
    mulcld
    #
    fsummulc2
    @20
    @2
    @5
    cL
    vn
    @24
    wph
    @55
    @19
    @56
    adantr
    #
    @30
    fsummulc1
    oveq12d
    @20
    @2
    @74
    @76
    vn
    @24
    @26
    @52
    @68
    cc
    wcel
    @74
    cc
    wcel
    @53
    @80
    cem
    @68
    mulcl
    sylancr
    @26
    @5
    cL
    @30
    @57
    mulcld
    fsumsub
    @20
    @2
    @78
    @48
    vn
    @26
    @78
    @5
    @42
    cmul
    co
    #
    @76
    cmin
    co
    @48
    @26
    @74
    @82
    @76
    cmin
    @26
    cem
    @5
    @7
    @52
    @26
    @53
    a1i
    @30
    @31
    mul12d
    oveq1d
    @26
    @5
    @42
    cL
    @30
    @54
    @57
    subdid
    eqtr4d
    sumeq2dv
    3eqtr2d
    mpteq2dva
    wph
    vx
    crp
    @70
    @72
    cc
    @20
    @52
    @69
    cc
    wcel
    @70
    cc
    wcel
    @53
    @20
    @2
    @68
    vn
    @24
    @80
    fsumcl
    #
    cem
    @69
    mulcl
    sylancr
    @20
    @71
    cL
    @20
    @2
    @5
    vn
    @24
    @30
    fsumcl
    #
    @81
    mulcld
    wph
    vx
    crp
    cem
    @69
    cc
    @79
    @83
    wph
    @41
    @52
    vx
    crp
    cem
    cmpt
    co1
    wcel
    rpssre
    @52
    wph
    @53
    a1i
    vx
    crp
    cem
    o1const
    sylancr
    vx
    crp
    @69
    cmpt
    co1
    wcel
    wph
    vx
    vn
    mulogsum
    a1i
    o1mul2
    wph
    vx
    crp
    @71
    cL
    cc
    @84
    @81
    vx
    crp
    @71
    cmpt
    co1
    wcel
    wph
    vx
    vn
    mudivsum
    a1i
    wph
    @41
    @55
    vx
    crp
    cL
    cmpt
    co1
    wcel
    rpssre
    @56
    vx
    crp
    cL
    o1const
    sylancr
    o1mul2
    o1sub2
    eqeltrrd
    o1sub2
    eqeltrrd
    o1mul2
    eqeltrrd
end
