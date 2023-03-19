include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cmu.mm"
include "cmul.mm"
include "csu.mm"
include "c2.mm"
include "clog.mm"
include "cmin.mm"
include "cmpt.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "co1.mm"
include "wcel.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "cz.mm"
include "elfznn.mm"
include "adantl.mm"
include "mucl.mm"
include "syl.mm"
include "zred.mm"
include "nndivred.mm"
include "recnd.mm"
include "cr.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "sylan2.mm"
include "relogcl.mm"
include "sqcld.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "cc.mm"
include "2cn.mm"
include "a1i.mm"
include "subcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addsubd.mm"
include "oveq2i.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "zcnd.mm"
include "addcld.mm"
include "rpcnne0d.mm"
include "w3a.mm"
include "divass.mm"
include "div23.mm"
include "eqtr3d.mm"
include "syl3anc.mm"
include "adddid.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "sumeq2dv.mm"
include "fsumadd.mm"
include "oveq1d.mm"
include "fsummulc2.mm"
include "fsumsub.mm"
include "oveq2d.mm"
include "mulcomd.mm"
include "mul12d.mm"
include "oveq12d.mm"
include "subdid.mm"
include "3eqtr4d.mm"
include "mpteq2ia.mm"
include "wtru.mm"
include "cvv.mm"
include "ovexd.mm"
include "mulog2sum.mm"
include "2ex.mm"
include "wss.mm"
include "rpssre.mm"
include "o1const.mm"
include "mp2an.mm"
include "cof.mm"
include "reex.mm"
include "ssexi.mm"
include "sumex.mm"
include "eqidd.mm"
include "offval2.mm"
include "mudivsum.mm"
include "mulogsum.mm"
include "o1sub.mm"
include "syl6eqelr.mm"
include "o1mul2.mm"
include "o1add2.mm"
include "trud.mm"
include "eqeltri.mm"

theorem selberglem1
  let vx: setvar x
  let cT: class T
  let vn: setvar n
  let vm: setvar m
  assume selberglem1.t: |- T = ( ( ( ( log ` ( x / n ) ) ^ 2 ) + ( 2 - ( 2 x. ( log ` ( x / n ) ) ) ) ) / n )

  disjoint n x
  disjoint m n
  disjoint m x
  assert |- ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( mmu ` n ) x. T ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

  proof
    vx
    crp
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
    cT
    cmul
    co
    #
    vn
    csu
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
    cmpt
    vx
    crp
    @2
    @4
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
    cmul
    co
    #
    vn
    csu
    #
    @8
    cmin
    co
    #
    c2
    @2
    @10
    vn
    csu
    #
    @2
    @10
    @12
    cmul
    co
    #
    vn
    csu
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    co1
    vx
    crp
    @9
    @22
    @0
    crp
    wcel
    #
    @15
    @2
    @10
    c2
    c2
    @12
    cmul
    co
    #
    cmin
    co
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
    @8
    cmin
    co
    @16
    @28
    caddc
    co
    @9
    @22
    @24
    @15
    @28
    @8
    @24
    @2
    @14
    vn
    @24
    c1
    @1
    fzfid
    #
    @24
    @3
    @2
    wcel
    #
    wa
    #
    @10
    @13
    @32
    @10
    @32
    @4
    @3
    @32
    @4
    @32
    @3
    cn
    wcel
    #
    @4
    cz
    wcel
    @31
    @33
    @24
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    mucl
    syl
    #
    zred
    @35
    nndivred
    recnd
    #
    @32
    @12
    @32
    @12
    @32
    @11
    crp
    wcel
    #
    @12
    cr
    wcel
    @31
    @24
    @3
    crp
    wcel
    @38
    @31
    @3
    @34
    nnrpd
    @0
    @3
    rpdivcl
    sylan2
    @11
    relogcl
    syl
    recnd
    #
    sqcld
    #
    mulcld
    #
    fsumcl
    @24
    @2
    @27
    vn
    @30
    @32
    @10
    @26
    @37
    @32
    c2
    @25
    c2
    cc
    wcel
    #
    @32
    2cn
    a1i
    #
    @32
    c2
    @12
    @43
    @39
    mulcld
    #
    subcld
    #
    mulcld
    #
    fsumcl
    @24
    @42
    @7
    cc
    wcel
    @8
    cc
    wcel
    2cn
    @24
    @7
    @0
    relogcl
    recnd
    c2
    @7
    mulcl
    sylancr
    addsubd
    @24
    @6
    @29
    @8
    cmin
    @24
    @6
    @2
    @14
    @27
    caddc
    co
    #
    vn
    csu
    @29
    @24
    @2
    @5
    @47
    vn
    @32
    @5
    @4
    @13
    @26
    caddc
    co
    #
    @3
    cdiv
    co
    #
    cmul
    co
    #
    @47
    cT
    @49
    @4
    cmul
    selberglem1.t
    oveq2i
    @32
    @50
    @10
    @48
    cmul
    co
    #
    @47
    @32
    @4
    cc
    wcel
    #
    @48
    cc
    wcel
    #
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    #
    @50
    @51
    wceq
    @32
    @4
    @36
    zcnd
    @32
    @13
    @26
    @40
    @45
    addcld
    @32
    @3
    @32
    @3
    @35
    nnrpd
    rpcnne0d
    @52
    @53
    @54
    w3a
    @4
    @48
    cmul
    co
    @3
    cdiv
    co
    @50
    @51
    @4
    @48
    @3
    divass
    @4
    @48
    @3
    div23
    eqtr3d
    syl3anc
    @32
    @10
    @13
    @26
    @37
    @40
    @45
    adddid
    eqtrd
    syl5eq
    sumeq2dv
    @24
    @2
    @14
    @27
    vn
    @30
    @41
    @46
    fsumadd
    eqtrd
    oveq1d
    @24
    @21
    @28
    @16
    caddc
    @24
    @2
    c2
    @10
    @18
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @21
    @28
    @24
    c2
    @2
    @55
    vn
    csu
    #
    cmul
    co
    @57
    @21
    @24
    @2
    @55
    c2
    vn
    @30
    @42
    @24
    2cn
    a1i
    @32
    @10
    @18
    @37
    @32
    @10
    @12
    @37
    @39
    mulcld
    #
    subcld
    fsummulc2
    @24
    @58
    @20
    c2
    cmul
    @24
    @2
    @10
    @18
    vn
    @30
    @37
    @59
    fsumsub
    oveq2d
    eqtr3d
    @24
    @2
    @56
    @27
    vn
    @32
    c2
    @10
    cmul
    co
    #
    c2
    @18
    cmul
    co
    #
    cmin
    co
    @10
    c2
    cmul
    co
    #
    @10
    @25
    cmul
    co
    #
    cmin
    co
    @56
    @27
    @32
    @60
    @62
    @61
    @63
    cmin
    @32
    c2
    @10
    @43
    @37
    mulcomd
    @32
    c2
    @10
    @12
    @43
    @37
    @39
    mul12d
    oveq12d
    @32
    c2
    @10
    @18
    @43
    @37
    @59
    subdid
    @32
    @10
    c2
    @25
    @37
    @43
    @44
    subdid
    3eqtr4d
    sumeq2dv
    eqtr3d
    oveq2d
    3eqtr4d
    mpteq2ia
    @23
    co1
    wcel
    wtru
    vx
    crp
    @16
    @21
    cvv
    wtru
    @24
    wa
    #
    @15
    @8
    cmin
    ovexd
    @64
    c2
    @20
    cmul
    ovexd
    vx
    crp
    @16
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    mulog2sum
    a1i
    wtru
    vx
    crp
    c2
    @20
    cvv
    c2
    cvv
    wcel
    @64
    2ex
    a1i
    @64
    @17
    @19
    cmin
    ovexd
    vx
    crp
    c2
    cmpt
    co1
    wcel
    #
    wtru
    crp
    cr
    wss
    @42
    @65
    rpssre
    2cn
    vx
    crp
    c2
    o1const
    mp2an
    a1i
    wtru
    vx
    crp
    @20
    cmpt
    vx
    crp
    @17
    cmpt
    #
    vx
    crp
    @19
    cmpt
    #
    cmin
    cof
    co
    #
    co1
    wtru
    vx
    crp
    @17
    @19
    cmin
    @66
    @67
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
    @17
    cvv
    wcel
    @64
    @2
    @10
    vn
    sumex
    a1i
    @19
    cvv
    wcel
    @64
    @2
    @18
    vn
    sumex
    a1i
    wtru
    @66
    eqidd
    wtru
    @67
    eqidd
    offval2
    @66
    co1
    wcel
    @67
    co1
    wcel
    @68
    co1
    wcel
    vx
    vn
    mudivsum
    vx
    vn
    mulogsum
    @66
    @67
    o1sub
    mp2an
    syl6eqelr
    o1mul2
    o1add2
    trud
    eqeltri
end
