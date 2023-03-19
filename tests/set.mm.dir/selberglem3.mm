include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cmu.mm"
include "cdiv.mm"
include "clog.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmin.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "rpre.mm"
include "wa.mm"
include "cz.mm"
include "ssrab2.mm"
include "simprr.mm"
include "sseldi.mm"
include "mucl.mm"
include "syl.mm"
include "zcnd.mm"
include "cc.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "ad2antrl.mm"
include "rpdivcld.mm"
include "relogcl.mm"
include "recnd.mm"
include "sqcld.mm"
include "mulcld.mm"
include "dvdsflsumcom.mm"
include "w3a.mm"
include "3ad2ant3.mm"
include "nncnd.mm"
include "3ad2ant2.mm"
include "nnne0d.mm"
include "divcan3d.mm"
include "2sumeq2dv.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "caddc.mm"
include "eqid.mm"
include "selberglem2.mm"
include "eqeltri.mm"

theorem selberglem3
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let vd: setvar d
  let vc: setvar c
  let vm: setvar m

  disjoint d n
  disjoint d x
  disjoint d y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint c d
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint d m
  disjoint m n
  disjoint m x
  disjoint m y
  assert |- ( x e. RR+ |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) sum_ d e. { y e. NN | y || n } ( ( mmu ` d ) x. ( ( log ` ( n / d ) ) ^ 2 ) ) / x ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

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
    vy
    cv
    vn
    cv
    #
    cdvds
    wbr
    #
    vy
    cn
    crab
    #
    vd
    cv
    #
    cmu
    cfv
    #
    @3
    @6
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
    vd
    csu
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
    c1
    @0
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    @7
    vm
    cv
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
    vm
    csu
    vd
    csu
    #
    @0
    cdiv
    co
    #
    @14
    cmin
    co
    #
    cmpt
    co1
    vx
    crp
    @15
    @25
    @0
    crp
    wcel
    #
    @13
    @24
    @14
    cmin
    @26
    @12
    @23
    @0
    cdiv
    @26
    @12
    @2
    @18
    @7
    @6
    @19
    cmul
    co
    #
    @6
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
    vm
    csu
    vd
    csu
    @23
    @26
    vy
    @0
    @11
    @31
    vm
    vn
    vd
    @3
    @27
    wceq
    #
    @10
    @30
    @7
    cmul
    @32
    @9
    @29
    c2
    cexp
    @32
    @8
    @28
    clog
    @3
    @27
    @6
    cdiv
    oveq1
    fveq2d
    oveq1d
    oveq2d
    @0
    rpre
    @26
    @3
    @2
    wcel
    #
    @6
    @5
    wcel
    #
    wa
    wa
    #
    @7
    @10
    @35
    @7
    @35
    @6
    cn
    wcel
    #
    @7
    cz
    wcel
    @35
    @5
    cn
    @6
    @4
    vy
    cn
    ssrab2
    @26
    @33
    @34
    simprr
    sseldi
    #
    @6
    mucl
    syl
    zcnd
    @35
    @9
    @35
    @8
    crp
    wcel
    #
    @9
    cc
    wcel
    @35
    @3
    @6
    @33
    @3
    crp
    wcel
    @26
    @34
    @33
    @3
    @3
    @1
    elfznn
    nnrpd
    ad2antrl
    @35
    @6
    @37
    nnrpd
    rpdivcld
    @38
    @9
    @8
    relogcl
    recnd
    syl
    sqcld
    mulcld
    dvdsflsumcom
    @26
    @2
    @18
    @31
    @22
    vd
    vm
    @26
    @6
    @2
    wcel
    #
    @19
    @18
    wcel
    #
    w3a
    #
    @30
    @21
    @7
    cmul
    @41
    @29
    @20
    c2
    cexp
    @41
    @28
    @19
    clog
    @41
    @19
    @6
    @41
    @19
    @40
    @26
    @19
    cn
    wcel
    @39
    @19
    @17
    elfznn
    3ad2ant3
    nncnd
    @41
    @6
    @39
    @26
    @36
    @40
    @6
    @1
    elfznn
    3ad2ant2
    #
    nncnd
    @41
    @6
    @42
    nnne0d
    divcan3d
    fveq2d
    oveq1d
    oveq2d
    2sumeq2dv
    eqtrd
    oveq1d
    oveq1d
    mpteq2ia
    vx
    @16
    clog
    cfv
    #
    c2
    cexp
    co
    c2
    c2
    @43
    cmul
    co
    cmin
    co
    caddc
    co
    @6
    cdiv
    co
    #
    vm
    vd
    @44
    eqid
    selberglem2
    eqeltri
end
