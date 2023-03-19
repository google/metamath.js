include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "simpr.mm"
include "oveq2.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "nn0cn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "w3a.mm"
include "divcan2.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "adantr.mm"
include "rspcedvd.mm"

theorem nn0enn0ex
  let vm: setvar m
  let cN: class N
  let vk: setvar k
  let vx: setvar x

  disjoint N m
  disjoint k x
  assert |- ( ( N e. NN0 /\ ( N / 2 ) e. NN0 ) -> E. m e. NN0 N = ( 2 x. m ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    wa
    #
    cN
    c2
    vm
    cv
    #
    cmul
    co
    #
    wceq
    cN
    c2
    @1
    cmul
    co
    #
    wceq
    #
    vm
    @1
    cn0
    @0
    @2
    simpr
    @3
    @4
    @1
    wceq
    #
    wa
    @5
    @6
    cN
    @8
    @5
    @6
    wceq
    @3
    @4
    @1
    c2
    cmul
    oveq2
    adantl
    eqeq2d
    @0
    @7
    @2
    @0
    cN
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @7
    cN
    nn0cn
    @0
    2cnd
    @11
    @0
    2ne0
    a1i
    @9
    @10
    @11
    w3a
    @6
    cN
    cN
    c2
    divcan2
    eqcomd
    syl3anc
    adantr
    rspcedvd
end
