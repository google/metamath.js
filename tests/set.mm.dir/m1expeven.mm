include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "caddc.mm"
include "zcn.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "expaddz.mm"
include "mpanl12.mm"
include "anidms.mm"
include "cpr.mm"
include "m1expcl2.mm"
include "wo.mm"
include "ovex.mm"
include "elpr.mm"
include "oveq12.mm"
include "neg1mulneg1e1.mm"
include "syl6eq.mm"
include "1t1e1.mm"
include "jaoi.mm"
include "sylbi.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem m1expeven
  let cN: class N


  assert |- ( N e. ZZ -> ( -u 1 ^ ( 2 x. N ) ) = 1 )

  proof
    cN
    cz
    wcel
    #
    c1
    cneg
    #
    c2
    cN
    cmul
    co
    #
    cexp
    co
    @1
    cN
    cN
    caddc
    co
    #
    cexp
    co
    #
    @1
    cN
    cexp
    co
    #
    @5
    cmul
    co
    #
    c1
    @0
    @2
    @3
    @1
    cexp
    @0
    cN
    cN
    zcn
    2timesd
    oveq2d
    @0
    @4
    @6
    wceq
    #
    @1
    cc
    wcel
    @1
    cc0
    wne
    @0
    @0
    wa
    @7
    neg1cn
    neg1ne0
    @1
    cN
    cN
    expaddz
    mpanl12
    anidms
    @0
    @5
    @1
    c1
    cpr
    wcel
    #
    @6
    c1
    wceq
    #
    cN
    m1expcl2
    @8
    @5
    @1
    wceq
    #
    @5
    c1
    wceq
    #
    wo
    @9
    @5
    @1
    c1
    @1
    cN
    cexp
    ovex
    elpr
    @10
    @9
    @11
    @10
    @6
    @1
    @1
    cmul
    co
    #
    c1
    @10
    @6
    @12
    wceq
    @5
    @1
    @5
    @1
    cmul
    oveq12
    anidms
    neg1mulneg1e1
    syl6eq
    @11
    @6
    c1
    c1
    cmul
    co
    #
    c1
    @11
    @6
    @13
    wceq
    @5
    c1
    @5
    c1
    cmul
    oveq12
    anidms
    1t1e1
    syl6eq
    jaoi
    sylbi
    syl
    3eqtrd
end
