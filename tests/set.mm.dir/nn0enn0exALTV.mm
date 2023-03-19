include "cn0.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdiv.mm"
include "nn0e.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
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

theorem nn0enn0exALTV
  let vm: setvar m
  let cN: class N
  let vk: setvar k
  let vx: setvar x

  disjoint N m
  disjoint k x
  assert |- ( ( N e. NN0 /\ N e. Even ) -> E. m e. NN0 N = ( 2 x. m ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    ceven
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
    #
    cN
    c2
    cN
    c2
    cdiv
    co
    #
    cmul
    co
    #
    wceq
    #
    vm
    @6
    cn0
    cN
    nn0e
    @3
    @6
    wceq
    #
    @5
    @8
    wb
    @2
    @9
    @4
    @7
    cN
    @3
    @6
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @0
    @8
    @1
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
    @8
    cN
    nn0cn
    @0
    2cnd
    @12
    @0
    2ne0
    a1i
    @10
    @11
    @12
    w3a
    @7
    cN
    cN
    c2
    divcan2
    eqcomd
    syl3anc
    adantr
    rspcedvd
end
