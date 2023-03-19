include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "cc.mm"
include "wceq.mm"
include "renegcl.mm"
include "reflcl.mm"
include "syl.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "negdi.mm"
include "sylancl.mm"
include "negcld.mm"
include "negsub.mm"
include "eqtr2d.mm"
include "wbr.mm"
include "peano2re.mm"
include "wa.mm"
include "flltp1.mm"
include "adantr.mm"
include "ltnegcon1.mm"
include "mpbid.mm"
include "mpdan.mm"
include "eqbrtrd.mm"

theorem ceim1l
  let cA: class A


  assert |- ( A e. RR -> ( -u ( |_ ` -u A ) - 1 ) < A )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cfl
    cfv
    #
    cneg
    #
    c1
    cmin
    co
    #
    @2
    c1
    caddc
    co
    #
    cneg
    #
    cA
    clt
    @0
    @6
    @3
    c1
    cneg
    caddc
    co
    #
    @4
    @0
    @2
    cc
    wcel
    c1
    cc
    wcel
    #
    @6
    @7
    wceq
    @0
    @2
    @0
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    cA
    renegcl
    #
    @1
    reflcl
    syl
    #
    recnd
    #
    ax-1cn
    @2
    c1
    negdi
    sylancl
    @0
    @3
    cc
    wcel
    @8
    @7
    @4
    wceq
    @0
    @2
    @13
    negcld
    ax-1cn
    @3
    c1
    negsub
    sylancl
    eqtr2d
    @0
    @5
    cr
    wcel
    #
    @6
    cA
    clt
    wbr
    #
    @0
    @10
    @14
    @12
    @2
    peano2re
    syl
    @0
    @14
    wa
    @1
    @5
    clt
    wbr
    #
    @15
    @0
    @16
    @14
    @0
    @9
    @16
    @11
    @1
    flltp1
    syl
    adantr
    cA
    @5
    ltnegcon1
    mpbid
    mpdan
    eqbrtrd
end
