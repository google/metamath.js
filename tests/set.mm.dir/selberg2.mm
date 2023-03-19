include "crp.mm"
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
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "vmacl.mm"
include "syl.mm"
include "recnd.mm"
include "nnrpd.mm"
include "relogcl.mm"
include "rpre.mm"
include "nndivre.mm"
include "syl2an.mm"
include "chpcl.mm"
include "addcld.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divcld.mm"
include "cc.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcld.mm"
include "sub32d.mm"
include "cc0.mm"
include "wne.mm"
include "rpcnne0.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "adddid.mm"
include "sumeq2dv.mm"
include "fsumadd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "pnncand.mm"
include "addcomd.mm"
include "3eqtrd.mm"
include "eqtr3d.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "selberg.mm"
include "selberg2lem.mm"
include "o1sub.mm"
include "mp2an.mm"
include "eqeltrri.mm"

theorem selberg2
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y

  disjoint n x
  disjoint c d
  disjoint c m
  disjoint c n
  disjoint c x
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
  assert |- ( x e. RR+ |-> ( ( ( ( ( psi ` x ) x. ( log ` x ) ) + sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. ( psi ` ( x / n ) ) ) ) / x ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

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
    cmpt
    #
    vx
    crp
    @2
    @4
    @5
    cmul
    co
    #
    vn
    csu
    #
    @0
    cchp
    cfv
    #
    @12
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
    cmpt
    #
    cmin
    cof
    co
    #
    vx
    crp
    @19
    @2
    @4
    @7
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
    @13
    cmin
    co
    #
    cmpt
    #
    co1
    @23
    vx
    crp
    @14
    @21
    cmin
    co
    #
    cmpt
    #
    @29
    @23
    @31
    wceq
    wtru
    vx
    crp
    @14
    @21
    cmin
    @15
    @22
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
    @11
    @13
    cmin
    ovexd
    @33
    @20
    @0
    cdiv
    ovexd
    wtru
    @15
    eqidd
    wtru
    @22
    eqidd
    offval2
    trud
    vx
    crp
    @30
    @28
    @32
    @30
    @11
    @21
    cmin
    co
    #
    @13
    cmin
    co
    @28
    @32
    @11
    @13
    @21
    @32
    @10
    @0
    @32
    @2
    @9
    vn
    @32
    c1
    @1
    fzfid
    #
    @32
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @8
    @37
    @4
    @37
    @3
    cn
    wcel
    #
    @4
    cr
    wcel
    @36
    @38
    @32
    @3
    @1
    elfznn
    #
    adantl
    #
    @3
    vmacl
    syl
    recnd
    #
    @37
    @5
    @7
    @37
    @5
    @37
    @3
    crp
    wcel
    @5
    cr
    wcel
    @37
    @3
    @40
    nnrpd
    @3
    relogcl
    syl
    recnd
    #
    @37
    @7
    @37
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    @32
    @0
    cr
    wcel
    #
    @38
    @43
    @36
    @0
    rpre
    #
    @39
    @0
    @3
    nndivre
    syl2an
    @6
    chpcl
    syl
    recnd
    #
    addcld
    mulcld
    fsumcl
    #
    @0
    rpcn
    #
    @0
    rpne0
    #
    divcld
    @32
    c2
    cc
    wcel
    @12
    cc
    wcel
    @13
    cc
    wcel
    2cn
    @32
    @12
    @0
    relogcl
    recnd
    #
    c2
    @12
    mulcl
    sylancr
    @32
    @20
    @0
    @32
    @17
    @19
    @32
    @2
    @16
    vn
    @35
    @37
    @4
    @5
    @41
    @42
    mulcld
    #
    fsumcl
    #
    @32
    @18
    @12
    @32
    @18
    @32
    @44
    @18
    cr
    wcel
    @45
    @0
    chpcl
    syl
    recnd
    @50
    mulcld
    #
    subcld
    #
    @48
    @49
    divcld
    sub32d
    @32
    @34
    @27
    @13
    cmin
    @32
    @10
    @20
    cmin
    co
    #
    @0
    cdiv
    co
    #
    @34
    @27
    @32
    @10
    cc
    wcel
    @20
    cc
    wcel
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    @56
    @34
    wceq
    @47
    @54
    @0
    rpcnne0
    @10
    @20
    @0
    divsubdir
    syl3anc
    @32
    @55
    @26
    @0
    cdiv
    @32
    @55
    @17
    @25
    caddc
    co
    #
    @20
    cmin
    co
    @25
    @19
    caddc
    co
    @26
    @32
    @10
    @57
    @20
    cmin
    @32
    @10
    @2
    @16
    @24
    caddc
    co
    #
    vn
    csu
    @57
    @32
    @2
    @9
    @58
    vn
    @37
    @4
    @5
    @7
    @41
    @42
    @46
    adddid
    sumeq2dv
    @32
    @2
    @16
    @24
    vn
    @35
    @51
    @37
    @4
    @7
    @41
    @46
    mulcld
    #
    fsumadd
    eqtrd
    oveq1d
    @32
    @17
    @25
    @19
    @52
    @32
    @2
    @24
    vn
    @35
    @59
    fsumcl
    #
    @53
    pnncand
    @32
    @25
    @19
    @60
    @53
    addcomd
    3eqtrd
    oveq1d
    eqtr3d
    oveq1d
    eqtrd
    mpteq2ia
    eqtri
    @15
    co1
    wcel
    @22
    co1
    wcel
    @23
    co1
    wcel
    vx
    vn
    selberg
    vx
    vn
    selberg2lem
    @15
    @22
    o1sub
    mp2an
    eqeltrri
end
