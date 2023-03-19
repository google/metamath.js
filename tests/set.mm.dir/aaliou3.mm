include "cn.mm"
include "c2.mm"
include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "caa.mm"
include "cmpt.mm"
include "c1.mm"
include "cfz.mm"
include "eqid.mm"
include "weq.mm"
include "fveq2.mm"
include "negeqd.mm"
include "oveq2d.mm"
include "cbvsumv.mm"
include "wcel.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "sumeq2i.mm"
include "eqtri.mm"
include "aaliou3lem9.mm"
include "nelir.mm"

theorem aaliou3
  let vk: setvar k
  let vi: setvar i
  let vj: setvar j
  let vl: setvar l


  assert |- sum_ k e. NN ( 2 ^ -u ( ! ` k ) ) e/ AA

  proof
    cn
    c2
    vk
    cv
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    vk
    csu
    #
    caa
    vj
    cn
    c2
    vj
    cv
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    cmpt
    #
    vl
    cn
    c1
    vl
    cv
    cfz
    co
    vi
    cv
    #
    @9
    cfv
    #
    vi
    csu
    cmpt
    #
    @4
    vj
    vi
    vl
    @9
    eqid
    #
    @4
    cn
    c2
    @10
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    vi
    csu
    cn
    @11
    vi
    csu
    cn
    @3
    @16
    vk
    vi
    vk
    vi
    weq
    #
    @2
    @15
    c2
    cexp
    @17
    @1
    @14
    @0
    @10
    cfa
    fveq2
    negeqd
    oveq2d
    cbvsumv
    cn
    @16
    @11
    vi
    @10
    cn
    wcel
    @11
    @16
    vj
    @10
    @8
    @16
    cn
    @9
    vj
    vi
    weq
    #
    @7
    @15
    c2
    cexp
    @18
    @6
    @14
    @5
    @10
    cfa
    fveq2
    negeqd
    oveq2d
    @13
    c2
    @15
    cexp
    ovex
    fvmpt
    eqcomd
    sumeq2i
    eqtri
    @12
    eqid
    aaliou3lem9
    nelir
end
