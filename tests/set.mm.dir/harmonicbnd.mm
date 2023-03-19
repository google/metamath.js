include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "cem.mm"
include "cicc.mm"
include "wcel.mm"
include "cn.mm"
include "wceq.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "wral.mm"
include "cmpt.mm"
include "wf.mm"
include "c2.mm"
include "caddc.mm"
include "eqid.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "emcllem7.mm"
include "simp2i.mm"
include "fmpt.mm"
include "mpbir.mm"
include "vtoclri.mm"

theorem harmonicbnd
  let vm: setvar m
  let cN: class N
  let vk: setvar k
  let vn: setvar n

  disjoint N m
  disjoint k m
  disjoint k n
  disjoint N k
  disjoint m n
  disjoint N n
  assert |- ( N e. NN -> ( sum_ m e. ( 1 ... N ) ( 1 / m ) - ( log ` N ) ) e. ( gamma [,] 1 ) )

  proof
    c1
    vn
    cv
    #
    cfz
    co
    #
    c1
    vm
    cv
    cdiv
    co
    #
    vm
    csu
    #
    @0
    clog
    cfv
    #
    cmin
    co
    #
    cem
    c1
    cicc
    co
    #
    wcel
    #
    c1
    cN
    cfz
    co
    #
    @2
    vm
    csu
    #
    cN
    clog
    cfv
    #
    cmin
    co
    #
    @6
    wcel
    vn
    cN
    cn
    @0
    cN
    wceq
    #
    @5
    @11
    @6
    @12
    @3
    @9
    @4
    @10
    cmin
    @12
    @1
    @8
    @2
    vm
    @0
    cN
    c1
    cfz
    oveq2
    sumeq1d
    @0
    cN
    clog
    fveq2
    oveq12d
    eleq1d
    @7
    vn
    cn
    wral
    cn
    @6
    vn
    cn
    @5
    cmpt
    #
    wf
    #
    cem
    c1
    c2
    clog
    cfv
    cmin
    co
    #
    c1
    cicc
    co
    wcel
    @14
    cn
    @15
    cem
    cicc
    co
    vn
    cn
    @3
    @0
    c1
    caddc
    co
    clog
    cfv
    cmin
    co
    cmpt
    #
    wf
    vk
    cn
    c1
    vk
    cv
    #
    cdiv
    co
    #
    c1
    @18
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    vm
    vn
    @13
    @16
    vn
    cn
    c1
    c1
    @0
    cdiv
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    cmpt
    #
    @13
    eqid
    #
    @16
    eqid
    @25
    eqid
    vk
    vn
    cn
    @21
    @22
    @24
    cmin
    co
    @17
    @0
    wceq
    #
    @18
    @22
    @20
    @24
    cmin
    @17
    @0
    c1
    cdiv
    oveq2
    #
    @27
    @19
    @23
    clog
    @27
    @18
    @22
    c1
    caddc
    @28
    oveq2d
    fveq2d
    oveq12d
    cbvmptv
    emcllem7
    simp2i
    vn
    cn
    @6
    @5
    @13
    @26
    fmpt
    mpbir
    vtoclri
end
