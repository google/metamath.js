include "cn0.mm"
include "wcel.mm"
include "codd.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "nn0oALTV.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "cc.mm"
include "nn0cn.mm"
include "peano2cnm.mm"
include "syl.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "npcan1.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "rspcedvd.mm"
include "syldan.mm"

theorem nn0onn0exALTV
  let vm: setvar m
  let cN: class N
  let vk: setvar k
  let vx: setvar x

  disjoint N m
  disjoint k x
  assert |- ( ( N e. NN0 /\ N e. Odd ) -> E. m e. NN0 N = ( ( 2 x. m ) + 1 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    codd
    wcel
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    cN
    c2
    vm
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vm
    cn0
    wrex
    cN
    nn0oALTV
    @0
    @3
    wa
    #
    @7
    cN
    c2
    @2
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vm
    @2
    cn0
    @0
    @3
    simpr
    @4
    @2
    wceq
    #
    @7
    @11
    wb
    @8
    @12
    @6
    @10
    cN
    @12
    @5
    @9
    c1
    caddc
    @4
    @2
    c2
    cmul
    oveq2
    oveq1d
    eqeq2d
    adantl
    @0
    @11
    @3
    @0
    @10
    @1
    c1
    caddc
    co
    #
    cN
    @0
    @9
    @1
    c1
    caddc
    @0
    @1
    c2
    @0
    cN
    cc
    wcel
    #
    @1
    cc
    wcel
    cN
    nn0cn
    #
    cN
    peano2cnm
    syl
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan2d
    oveq1d
    @0
    @14
    @13
    cN
    wceq
    @15
    cN
    npcan1
    syl
    eqtr2d
    adantr
    rspcedvd
    syldan
end
