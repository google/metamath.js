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
include "crp.mm"
include "wa.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "1rp.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "eliooord.mm"
include "simpld.mm"
include "ltled.mm"
include "rpgecld.mm"
include "ex.mm"
include "ssrdv.mm"
include "vmadivsum.mm"
include "o1res2.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "vmacl.mm"
include "syl.mm"
include "nndivred.mm"
include "recnd.mm"
include "fsumcl.mm"
include "relogcld.mm"
include "subcld.mm"
include "nnrpd.mm"
include "remulcld.mm"
include "fsumrecl.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "rehalfcld.mm"
include "resubcld.mm"
include "nnncan2d.mm"
include "caddc.mm"
include "subsub4d.mm"
include "2halvesd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "sub32d.mm"
include "adantr.mm"
include "fsumsub.mm"
include "relogdivd.mm"
include "cc.mm"
include "subdid.mm"
include "sumeq2dv.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "fsummulc1.mm"
include "3eqtr4d.mm"
include "mulcld.mm"
include "rpne0d.mm"
include "divsubdird.mm"
include "divcan4d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "mpteq2dva.mm"
include "vmalogdivsum2.mm"
include "syl6eqel.mm"
include "o1dif.mm"
include "mpbid.mm"
include "trud.mm"

theorem vmalogdivsum
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
  assert |- ( x e. ( 1 (,) +oo ) |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( ( Lam ` n ) / n ) x. ( log ` n ) ) / ( log ` x ) ) - ( ( log ` x ) / 2 ) ) ) e. O(1)

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
    @4
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
    @10
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
    @6
    vn
    csu
    #
    @10
    cmin
    co
    #
    cmpt
    co1
    wcel
    @14
    wtru
    vx
    @0
    crp
    @16
    wtru
    vx
    @0
    crp
    wtru
    @1
    @0
    wcel
    #
    @1
    crp
    wcel
    #
    wtru
    @17
    wa
    #
    @1
    c1
    @17
    @1
    cr
    wcel
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
    @19
    1rp
    a1i
    @19
    c1
    @1
    @19
    1red
    @20
    @19
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
    @17
    @21
    @22
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
    ex
    ssrdv
    vx
    crp
    @16
    cmpt
    co1
    wcel
    wtru
    vx
    vn
    vmadivsum
    a1i
    o1res2
    wtru
    vx
    @0
    @16
    @13
    @19
    @15
    @10
    @19
    @3
    @6
    vn
    @19
    c1
    @2
    fzfid
    #
    @19
    @4
    @3
    wcel
    #
    wa
    #
    @6
    @27
    @5
    @4
    @27
    @4
    cn
    wcel
    #
    @5
    cr
    wcel
    @26
    @28
    @19
    @4
    @2
    elfznn
    adantl
    #
    @4
    vmacl
    syl
    #
    @29
    nndivred
    #
    recnd
    #
    fsumcl
    #
    @19
    @10
    @19
    @1
    @24
    relogcld
    #
    recnd
    #
    subcld
    @19
    @13
    @19
    @11
    @12
    @19
    @9
    @10
    @19
    @3
    @8
    vn
    @25
    @27
    @6
    @7
    @31
    @27
    @4
    @27
    @4
    @29
    nnrpd
    #
    relogcld
    #
    remulcld
    #
    fsumrecl
    #
    @19
    @1
    @20
    @23
    rplogcld
    #
    rerpdivcld
    #
    @19
    @10
    @34
    rehalfcld
    #
    resubcld
    recnd
    wtru
    vx
    @0
    @16
    @13
    cmin
    co
    #
    cmpt
    vx
    @0
    @3
    @6
    @1
    @4
    cdiv
    co
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    @10
    cdiv
    co
    #
    @12
    cmin
    co
    #
    cmpt
    co1
    wtru
    vx
    @0
    @43
    @48
    @19
    @15
    @12
    cmin
    co
    #
    @12
    cmin
    co
    #
    @13
    cmin
    co
    @49
    @11
    cmin
    co
    #
    @43
    @48
    @19
    @49
    @11
    @12
    @19
    @15
    @12
    @33
    @19
    @12
    @42
    recnd
    #
    subcld
    @19
    @11
    @41
    recnd
    #
    @52
    nnncan2d
    @19
    @50
    @16
    @13
    cmin
    @19
    @50
    @15
    @12
    @12
    caddc
    co
    #
    cmin
    co
    @16
    @19
    @15
    @12
    @12
    @33
    @52
    @52
    subsub4d
    @19
    @54
    @10
    @15
    cmin
    @19
    @10
    @35
    2halvesd
    oveq2d
    eqtrd
    oveq1d
    @19
    @51
    @15
    @11
    cmin
    co
    #
    @12
    cmin
    co
    @48
    @19
    @15
    @12
    @11
    @33
    @52
    @53
    sub32d
    @19
    @47
    @55
    @12
    cmin
    @19
    @47
    @15
    @10
    cmul
    co
    #
    @9
    cmin
    co
    #
    @10
    cdiv
    co
    @56
    @10
    cdiv
    co
    #
    @11
    cmin
    co
    @55
    @19
    @46
    @57
    @10
    cdiv
    @19
    @3
    @6
    @10
    cmul
    co
    #
    @8
    cmin
    co
    #
    vn
    csu
    @3
    @59
    vn
    csu
    #
    @9
    cmin
    co
    @46
    @57
    @19
    @3
    @59
    @8
    vn
    @25
    @27
    @59
    @27
    @6
    @10
    @31
    @27
    @1
    @19
    @18
    @26
    @24
    adantr
    #
    relogcld
    remulcld
    recnd
    @27
    @8
    @38
    recnd
    fsumsub
    @19
    @3
    @45
    @60
    vn
    @27
    @45
    @6
    @10
    @7
    cmin
    co
    #
    cmul
    co
    @60
    @27
    @44
    @63
    @6
    cmul
    @27
    @1
    @4
    @62
    @36
    relogdivd
    oveq2d
    @27
    @6
    @10
    @7
    @32
    @19
    @10
    cc
    wcel
    @26
    @35
    adantr
    @27
    @7
    @37
    recnd
    subdid
    eqtrd
    sumeq2dv
    @19
    @56
    @61
    @9
    cmin
    @19
    @3
    @6
    @10
    vn
    @25
    @35
    @27
    @5
    @4
    @27
    @5
    @30
    recnd
    @27
    @4
    @29
    nncnd
    @27
    @4
    @29
    nnne0d
    divcld
    fsummulc1
    oveq1d
    3eqtr4d
    oveq1d
    @19
    @56
    @9
    @10
    @19
    @15
    @10
    @33
    @35
    mulcld
    @19
    @9
    @39
    recnd
    @35
    @19
    @10
    @40
    rpne0d
    #
    divsubdird
    @19
    @58
    @15
    @11
    cmin
    @19
    @15
    @10
    @33
    @35
    @64
    divcan4d
    oveq1d
    3eqtrd
    oveq1d
    eqtr4d
    3eqtr3d
    mpteq2dva
    vx
    vn
    vmalogdivsum2
    syl6eqel
    o1dif
    mpbid
    trud
end
