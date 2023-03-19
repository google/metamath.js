include "cem.mm"
include "c1.mm"
include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "cfz.mm"
include "cdiv.mm"
include "csu.mm"
include "cmpt.mm"
include "wf.mm"
include "caddc.mm"
include "eqid.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "emcllem7.mm"
include "simp1i.mm"

theorem emcl
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cN: class N


  assert |- gamma e. ( ( 1 - ( log ` 2 ) ) [,] 1 )

  proof
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
    cn
    cem
    c1
    cicc
    co
    vn
    cn
    c1
    vn
    cv
    #
    cfz
    co
    c1
    vm
    cv
    cdiv
    co
    vm
    csu
    #
    @1
    clog
    cfv
    cmin
    co
    cmpt
    #
    wf
    cn
    @0
    cem
    cicc
    co
    vn
    cn
    @2
    @1
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
    @6
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
    @3
    @4
    vn
    cn
    c1
    c1
    @1
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
    @3
    eqid
    @4
    eqid
    @13
    eqid
    vk
    vn
    cn
    @9
    @10
    @12
    cmin
    co
    vk
    vn
    weq
    #
    @6
    @10
    @8
    @12
    cmin
    @5
    @1
    c1
    cdiv
    oveq2
    #
    @14
    @7
    @11
    clog
    @14
    @6
    @10
    c1
    caddc
    @15
    oveq2d
    fveq2d
    oveq12d
    cbvmptv
    emcllem7
    simp1i
end
