include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "clog.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "csu.mm"
include "caddc.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "wa.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "chpcl.mm"
include "syl.mm"
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
include "relogcld.mm"
include "remulcld.mm"
include "recnd.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "vmacl.mm"
include "adantr.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "2re.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "nnrpd.mm"
include "resubcld.mm"
include "addassd.mm"
include "2cnd.mm"
include "rpne0d.mm"
include "divcld.mm"
include "mulcld.mm"
include "pncan3d.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "oveq1d.mm"
include "readdcld.mm"
include "divdird.mm"
include "eqtrd.mm"
include "addsubd.mm"
include "mpteq2dva.mm"
include "ex.mm"
include "ssrdv.mm"
include "selberg2.mm"
include "o1res2.mm"
include "selberg3lem2.mm"
include "o1add2.mm"
include "eqeltrd.mm"
include "trud.mm"

theorem selberg3
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
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( ( ( ( psi ` x ) x. ( log ` x ) ) + ( ( 2 / ( log ` x ) ) x. sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) x. ( psi ` ( x / n ) ) ) x. ( log ` n ) ) ) ) / x ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

  proof
    vx
    c1
    cpnf
    cioo
    co
    #
    vx
    cv
    #
    cchp
    cfv
    #
    @1
    clog
    cfv
    #
    cmul
    co
    #
    c2
    @3
    cdiv
    co
    #
    c1
    @1
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
    @1
    @8
    cdiv
    co
    #
    cchp
    cfv
    #
    cmul
    co
    #
    @8
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    caddc
    co
    #
    @1
    cdiv
    co
    #
    c2
    @3
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    #
    co1
    wcel
    wtru
    @21
    vx
    @0
    @4
    @7
    @12
    vn
    csu
    #
    caddc
    co
    #
    @1
    cdiv
    co
    #
    @19
    cmin
    co
    #
    @16
    @22
    cmin
    co
    #
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @20
    @28
    wtru
    @1
    @0
    wcel
    #
    wa
    #
    @20
    @24
    @27
    caddc
    co
    #
    @19
    cmin
    co
    @28
    @30
    @18
    @31
    @19
    cmin
    @30
    @18
    @23
    @26
    caddc
    co
    #
    @1
    cdiv
    co
    @31
    @30
    @17
    @32
    @1
    cdiv
    @30
    @32
    @4
    @22
    @26
    caddc
    co
    #
    caddc
    co
    @17
    @30
    @4
    @22
    @26
    @30
    @4
    @30
    @2
    @3
    @30
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    @29
    @34
    wtru
    @1
    c1
    cpnf
    elioore
    adantl
    #
    @1
    chpcl
    syl
    @30
    @1
    @30
    @1
    c1
    @35
    c1
    crp
    wcel
    @30
    1rp
    a1i
    @30
    c1
    @1
    @30
    1red
    @35
    @30
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
    @29
    @36
    @37
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
    remulcld
    #
    recnd
    @30
    @22
    @30
    @7
    @12
    vn
    @30
    c1
    @6
    fzfid
    #
    @30
    @8
    @7
    wcel
    #
    wa
    #
    @9
    @11
    @44
    @8
    cn
    wcel
    #
    @9
    cr
    wcel
    @43
    @45
    @30
    @8
    @6
    elfznn
    adantl
    #
    @8
    vmacl
    syl
    @44
    @10
    cr
    wcel
    @11
    cr
    wcel
    @44
    @1
    @8
    @30
    @34
    @43
    @35
    adantr
    @46
    nndivred
    @10
    chpcl
    syl
    remulcld
    #
    fsumrecl
    #
    recnd
    #
    @30
    @26
    @30
    @16
    @22
    @30
    @5
    @15
    @30
    c2
    @3
    c2
    cr
    wcel
    @30
    2re
    a1i
    #
    @30
    @1
    @35
    @38
    rplogcld
    #
    rerpdivcld
    @30
    @7
    @14
    vn
    @42
    @44
    @12
    @13
    @47
    @44
    @8
    @44
    @8
    @46
    nnrpd
    relogcld
    remulcld
    fsumrecl
    #
    remulcld
    @48
    resubcld
    #
    recnd
    #
    addassd
    @30
    @33
    @16
    @4
    caddc
    @30
    @22
    @16
    @49
    @30
    @5
    @15
    @30
    c2
    @3
    @30
    2cnd
    @30
    @3
    @40
    recnd
    @30
    @3
    @51
    rpne0d
    divcld
    @30
    @15
    @52
    recnd
    mulcld
    pncan3d
    oveq2d
    eqtr2d
    oveq1d
    @30
    @23
    @26
    @1
    @30
    @23
    @30
    @4
    @22
    @41
    @48
    readdcld
    #
    recnd
    @54
    @30
    @1
    @35
    recnd
    @30
    @1
    @39
    rpne0d
    divdird
    eqtrd
    oveq1d
    @30
    @24
    @27
    @19
    @30
    @24
    @30
    @23
    @1
    @55
    @39
    rerpdivcld
    #
    recnd
    @30
    @27
    @30
    @26
    @1
    @53
    @39
    rerpdivcld
    #
    recnd
    @30
    @19
    @30
    c2
    @3
    @50
    @40
    remulcld
    #
    recnd
    addsubd
    eqtrd
    mpteq2dva
    wtru
    vx
    @0
    @25
    @27
    cr
    @30
    @24
    @19
    @56
    @58
    resubcld
    @57
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
    @29
    @1
    crp
    wcel
    @39
    ex
    ssrdv
    vx
    crp
    @25
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    selberg2
    a1i
    o1res2
    vx
    @0
    @27
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    selberg3lem2
    a1i
    o1add2
    eqeltrd
    trud
end
