include "cn0.mm"
include "clt.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cbc.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cwrecs.mm"
include "csb.mm"
include "weq.mm"
include "fvex.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "sumeq2sdv.mm"
include "csbie.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "dmeq.mm"
include "wcel.mm"
include "fveq1.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "syl5eq.mm"
include "csbeq2dv.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "csbeq1d.mm"
include "eqtrd.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "bpolylem.mm"

theorem bpolyval
  let vk: setvar k
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cF: class F
  let vc: setvar c

  disjoint N k
  disjoint X k
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint F g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint N g
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint c g
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint X c
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X x
  assert |- ( ( N e. NN0 /\ X e. CC ) -> ( N BernPoly X ) = ( ( X ^ N ) - sum_ k e. ( 0 ... ( N - 1 ) ) ( ( N _C k ) x. ( ( k BernPoly X ) / ( ( N - k ) + 1 ) ) ) ) )

  proof
    vg
    vk
    vn
    cn0
    clt
    vc
    cvv
    cX
    vc
    cv
    #
    cdm
    #
    chash
    cfv
    #
    cexp
    co
    #
    @1
    @2
    vm
    cv
    #
    cbc
    co
    #
    @4
    @0
    cfv
    #
    @2
    @4
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmin
    co
    #
    cmpt
    #
    cwrecs
    #
    @13
    cN
    cX
    vc
    vg
    cvv
    @12
    vn
    vg
    cv
    #
    cdm
    #
    chash
    cfv
    #
    cX
    vn
    cv
    #
    cexp
    co
    #
    @16
    @18
    vk
    cv
    #
    cbc
    co
    #
    @20
    @15
    cfv
    #
    @18
    @20
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    csb
    #
    vc
    vg
    weq
    #
    @12
    vn
    @2
    @28
    csb
    #
    @29
    @30
    @12
    vn
    @2
    @19
    @1
    @18
    @4
    cbc
    co
    #
    @6
    @18
    @4
    cmin
    co
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmin
    co
    #
    csb
    @31
    vn
    @2
    @38
    @12
    @1
    chash
    fvex
    @18
    @2
    wceq
    #
    @19
    @3
    @37
    @11
    cmin
    @18
    @2
    cX
    cexp
    oveq2
    @39
    @1
    @36
    @10
    vm
    @39
    @32
    @5
    @35
    @9
    cmul
    @18
    @2
    @4
    cbc
    oveq1
    @39
    @34
    @8
    @6
    cdiv
    @39
    @33
    @7
    c1
    caddc
    @18
    @2
    @4
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq12d
    sumeq2sdv
    oveq12d
    csbie
    @30
    vn
    @2
    @38
    @28
    @30
    @37
    @27
    @19
    cmin
    @30
    @37
    @1
    @21
    @20
    @0
    cfv
    #
    @24
    cdiv
    co
    #
    cmul
    co
    #
    vk
    csu
    @27
    @1
    @36
    @42
    vm
    vk
    vm
    vk
    weq
    #
    @32
    @21
    @35
    @41
    cmul
    @4
    @20
    @18
    cbc
    oveq2
    @43
    @6
    @40
    @34
    @24
    cdiv
    @4
    @20
    @0
    fveq2
    @43
    @33
    @23
    c1
    caddc
    @4
    @20
    @18
    cmin
    oveq2
    oveq1d
    oveq12d
    oveq12d
    cbvsumv
    @30
    @1
    @16
    @42
    @26
    vk
    @0
    @15
    dmeq
    #
    @30
    @42
    @26
    wceq
    @20
    @1
    wcel
    @30
    @41
    @25
    @21
    cmul
    @30
    @40
    @22
    @24
    cdiv
    @20
    @0
    @15
    fveq1
    oveq1d
    oveq2d
    adantr
    sumeq12dv
    syl5eq
    oveq2d
    csbeq2dv
    syl5eqr
    @30
    vn
    @2
    @17
    @28
    @30
    @1
    @16
    chash
    @44
    fveq2d
    csbeq1d
    eqtrd
    cbvmptv
    @14
    eqid
    bpolylem
end
