include "crp.mm"
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
include "cmpt.mm"
include "cof.mm"
include "co1.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "cr.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "a1i.mm"
include "wa.mm"
include "ovexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "trud.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "recnd.mm"
include "relogcl.mm"
include "mulcld.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "rpre.mm"
include "nndivre.mm"
include "syl2an.mm"
include "chpcl.mm"
include "fsumcl.mm"
include "addcld.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divcld.mm"
include "nndivred.mm"
include "nnncan2d.mm"
include "subsub4d.mm"
include "pntrval.mm"
include "oveq1d.mm"
include "subdird.mm"
include "eqtrd.mm"
include "addsubd.mm"
include "eqtr4d.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "rpcnne0.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "divcan3d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "addsubassd.mm"
include "adantr.mm"
include "fsumsub.mm"
include "subdid.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sylan2.mm"
include "div12.mm"
include "sumeq2dv.mm"
include "fsummulc2.mm"
include "3eqtr4rd.mm"
include "3eqtr3rd.mm"
include "3eqtr3d.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "selberg2.mm"
include "vmadivsum.mm"
include "o1sub.mm"
include "mp2an.mm"
include "eqeltrri.mm"

theorem selbergr
  let vx: setvar x
  let cR: class R
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint a d
  disjoint a x
  disjoint d x
  disjoint R d
  disjoint R x
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint A a
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
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
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint R c
  disjoint d y
  disjoint k y
  disjoint R k
  disjoint m y
  disjoint R m
  disjoint n y
  disjoint R n
  disjoint x y
  disjoint R y
  assert |- ( x e. RR+ |-> ( ( ( ( R ` x ) x. ( log ` x ) ) + sum_ d e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` d ) x. ( R ` ( x / d ) ) ) ) / x ) ) e. O(1)

  proof
    vx
    crp
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
    vd
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
    vd
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
    cmpt
    #
    vx
    crp
    @5
    @7
    @6
    cdiv
    co
    #
    vd
    csu
    #
    @2
    cmin
    co
    #
    cmpt
    #
    cmin
    cof
    co
    #
    vx
    crp
    @0
    cR
    cfv
    #
    @2
    cmul
    co
    #
    @5
    @7
    @8
    cR
    cfv
    #
    cmul
    co
    #
    vd
    csu
    #
    caddc
    co
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    co1
    @21
    vx
    crp
    @15
    @19
    cmin
    co
    #
    cmpt
    #
    @29
    @21
    @31
    wceq
    wtru
    vx
    crp
    @15
    @19
    cmin
    @16
    @20
    cvv
    cvv
    cvv
    crp
    cvv
    wcel
    wtru
    crp
    cr
    reex
    rpssre
    ssexi
    a1i
    wtru
    @0
    crp
    wcel
    #
    wa
    #
    @13
    @14
    cmin
    ovexd
    @33
    @18
    @2
    cmin
    ovexd
    wtru
    @16
    eqidd
    wtru
    @20
    eqidd
    offval2
    trud
    vx
    crp
    @30
    @28
    @32
    @23
    @11
    caddc
    co
    #
    @0
    cdiv
    co
    #
    @2
    cmin
    co
    #
    @19
    cmin
    co
    @35
    @18
    cmin
    co
    #
    @30
    @28
    @32
    @35
    @18
    @2
    @32
    @34
    @0
    @32
    @23
    @11
    @32
    @22
    @2
    @32
    @22
    crp
    cr
    @0
    cR
    cR
    va
    pntrval.r
    pntrf
    ffvelrni
    recnd
    @32
    @2
    @0
    relogcl
    recnd
    #
    mulcld
    #
    @32
    @5
    @10
    vd
    @32
    c1
    @4
    fzfid
    #
    @32
    @6
    @5
    wcel
    #
    wa
    #
    @7
    @9
    @42
    @7
    @42
    @6
    cn
    wcel
    #
    @7
    cr
    wcel
    @41
    @43
    @32
    @6
    @4
    elfznn
    #
    adantl
    #
    @6
    vmacl
    syl
    #
    recnd
    #
    @42
    @9
    @42
    @8
    cr
    wcel
    #
    @9
    cr
    wcel
    @32
    @0
    cr
    wcel
    #
    @43
    @48
    @41
    @0
    rpre
    #
    @44
    @0
    @6
    nndivre
    syl2an
    #
    @8
    chpcl
    syl
    recnd
    #
    mulcld
    #
    fsumcl
    #
    addcld
    #
    @0
    rpcn
    #
    @0
    rpne0
    #
    divcld
    @32
    @5
    @17
    vd
    @40
    @42
    @17
    @42
    @7
    @6
    @46
    @45
    nndivred
    recnd
    #
    fsumcl
    #
    @38
    nnncan2d
    @32
    @36
    @15
    @19
    cmin
    @32
    @13
    @2
    cmin
    co
    #
    @2
    cmin
    co
    @13
    @2
    @2
    caddc
    co
    #
    cmin
    co
    @36
    @15
    @32
    @13
    @2
    @2
    @32
    @12
    @0
    @32
    @3
    @11
    @32
    @1
    @2
    @32
    @1
    @32
    @49
    @1
    cr
    wcel
    @50
    @0
    chpcl
    syl
    recnd
    #
    @38
    mulcld
    #
    @54
    addcld
    #
    @56
    @57
    divcld
    @38
    @38
    subsub4d
    @32
    @35
    @60
    @2
    cmin
    @32
    @35
    @12
    @0
    @2
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
    @13
    @65
    @0
    cdiv
    co
    #
    cmin
    co
    #
    @60
    @32
    @34
    @66
    @0
    cdiv
    @32
    @34
    @3
    @65
    cmin
    co
    #
    @11
    caddc
    co
    @66
    @32
    @23
    @70
    @11
    caddc
    @32
    @23
    @1
    @0
    cmin
    co
    #
    @2
    cmul
    co
    @70
    @32
    @22
    @71
    @2
    cmul
    @0
    cR
    va
    pntrval.r
    pntrval
    oveq1d
    @32
    @1
    @0
    @2
    @62
    @56
    @38
    subdird
    eqtrd
    oveq1d
    @32
    @3
    @11
    @65
    @63
    @54
    @32
    @0
    @2
    @56
    @38
    mulcld
    #
    addsubd
    eqtr4d
    oveq1d
    @32
    @12
    cc
    wcel
    @65
    cc
    wcel
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    wa
    #
    @67
    @69
    wceq
    @64
    @72
    @0
    rpcnne0
    #
    @12
    @65
    @0
    divsubdir
    syl3anc
    @32
    @68
    @2
    @13
    cmin
    @32
    @2
    @0
    @38
    @56
    @57
    divcan3d
    oveq2d
    3eqtrd
    oveq1d
    @32
    @14
    @61
    @13
    cmin
    @32
    @2
    @38
    2timesd
    oveq2d
    3eqtr4d
    oveq1d
    @32
    @34
    @0
    @18
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
    @35
    @76
    @0
    cdiv
    co
    #
    cmin
    co
    #
    @28
    @37
    @32
    @34
    cc
    wcel
    @76
    cc
    wcel
    @74
    @78
    @80
    wceq
    @55
    @32
    @0
    @18
    @56
    @59
    mulcld
    #
    @75
    @34
    @76
    @0
    divsubdir
    syl3anc
    @32
    @77
    @27
    @0
    cdiv
    @32
    @77
    @23
    @11
    @76
    cmin
    co
    #
    caddc
    co
    @27
    @32
    @23
    @11
    @76
    @39
    @54
    @81
    addsubassd
    @32
    @82
    @26
    @23
    caddc
    @32
    @5
    @10
    @0
    @17
    cmul
    co
    #
    cmin
    co
    #
    vd
    csu
    @11
    @5
    @83
    vd
    csu
    #
    cmin
    co
    @26
    @82
    @32
    @5
    @10
    @83
    vd
    @40
    @53
    @42
    @0
    @17
    @32
    @73
    @41
    @56
    adantr
    #
    @58
    mulcld
    fsumsub
    @32
    @5
    @25
    @84
    vd
    @42
    @7
    @9
    @8
    cmin
    co
    #
    cmul
    co
    @10
    @7
    @8
    cmul
    co
    #
    cmin
    co
    @25
    @84
    @42
    @7
    @9
    @8
    @47
    @52
    @42
    @8
    @51
    recnd
    subdid
    @42
    @24
    @87
    @7
    cmul
    @42
    @8
    crp
    wcel
    #
    @24
    @87
    wceq
    @41
    @32
    @6
    crp
    wcel
    #
    @89
    @41
    @6
    @44
    nnrpd
    @0
    @6
    rpdivcl
    sylan2
    @8
    cR
    va
    pntrval.r
    pntrval
    syl
    oveq2d
    @42
    @83
    @88
    @10
    cmin
    @42
    @73
    @7
    cc
    wcel
    @6
    cc
    wcel
    @6
    cc0
    wne
    wa
    #
    @83
    @88
    wceq
    @86
    @47
    @42
    @90
    @91
    @42
    @6
    @45
    nnrpd
    @6
    rpcnne0
    syl
    @0
    @7
    @6
    div12
    syl3anc
    oveq2d
    3eqtr4d
    sumeq2dv
    @32
    @76
    @85
    @11
    cmin
    @32
    @5
    @17
    @0
    vd
    @40
    @56
    @58
    fsummulc2
    oveq2d
    3eqtr4rd
    oveq2d
    eqtrd
    oveq1d
    @32
    @79
    @18
    @35
    cmin
    @32
    @18
    @0
    @59
    @56
    @57
    divcan3d
    oveq2d
    3eqtr3rd
    3eqtr3d
    mpteq2ia
    eqtri
    @16
    co1
    wcel
    @20
    co1
    wcel
    @21
    co1
    wcel
    vx
    vd
    selberg2
    vx
    vd
    vmadivsum
    @16
    @20
    o1sub
    mp2an
    eqeltrri
end
