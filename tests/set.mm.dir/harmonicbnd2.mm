include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cdiv.mm"
include "csu.mm"
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "c2.mm"
include "cem.mm"
include "cicc.mm"
include "wcel.mm"
include "cn.mm"
include "wceq.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "wral.mm"
include "cmpt.mm"
include "wf.mm"
include "eqid.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "emcllem7.mm"
include "simp3i.mm"
include "fmpt.mm"
include "mpbir.mm"
include "vtoclri.mm"

theorem harmonicbnd2
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
  assert |- ( N e. NN -> ( sum_ m e. ( 1 ... N ) ( 1 / m ) - ( log ` ( N + 1 ) ) ) e. ( ( 1 - ( log ` 2 ) ) [,] gamma ) )

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
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    c1
    c2
    clog
    cfv
    cmin
    co
    #
    cem
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
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    @8
    wcel
    vn
    cN
    cn
    @0
    cN
    wceq
    #
    @6
    @14
    @8
    @15
    @3
    @11
    @5
    @13
    cmin
    @15
    @1
    @10
    @2
    vm
    @0
    cN
    c1
    cfz
    oveq2
    sumeq1d
    @15
    @4
    @12
    clog
    @0
    cN
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    eleq1d
    @9
    vn
    cn
    wral
    cn
    @8
    vn
    cn
    @6
    cmpt
    #
    wf
    #
    cem
    @7
    c1
    cicc
    co
    wcel
    cn
    cem
    c1
    cicc
    co
    vn
    cn
    @3
    @0
    clog
    cfv
    cmin
    co
    cmpt
    #
    wf
    @17
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
    @20
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
    @18
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
    @18
    eqid
    @16
    eqid
    #
    @27
    eqid
    vk
    vn
    cn
    @23
    @24
    @26
    cmin
    co
    @19
    @0
    wceq
    #
    @20
    @24
    @22
    @26
    cmin
    @19
    @0
    c1
    cdiv
    oveq2
    #
    @29
    @21
    @25
    clog
    @29
    @20
    @24
    c1
    caddc
    @30
    oveq2d
    fveq2d
    oveq12d
    cbvmptv
    emcllem7
    simp3i
    vn
    cn
    @8
    @6
    @16
    @28
    fmpt
    mpbir
    vtoclri
end
