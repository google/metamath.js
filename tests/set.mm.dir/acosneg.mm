include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "casin.mm"
include "cfv.mm"
include "cmin.mm"
include "cacos.mm"
include "caddc.mm"
include "wceq.mm"
include "picn.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "asincl.mm"
include "subneg.mm"
include "sylancr.mm"
include "asinneg.mm"
include "oveq2d.mm"
include "a1i.mm"
include "subsubd.mm"
include "pidiv2halves.mm"
include "subaddrii.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "3eqtr4d.mm"
include "negcl.mm"
include "acosval.mm"
include "syl.mm"

theorem acosneg
  let cA: class A


  assert |- ( A e. CC -> ( arccos ` -u A ) = ( _pi - ( arccos ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cpi
    c2
    cdiv
    co
    #
    cA
    cneg
    #
    casin
    cfv
    #
    cmin
    co
    #
    cpi
    @1
    cA
    casin
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    @2
    cacos
    cfv
    #
    cpi
    cA
    cacos
    cfv
    #
    cmin
    co
    @0
    @1
    @5
    cneg
    #
    cmin
    co
    #
    @1
    @5
    caddc
    co
    #
    @4
    @7
    @0
    @1
    cc
    wcel
    #
    @5
    cc
    wcel
    @11
    @12
    wceq
    cpi
    cc
    wcel
    #
    @13
    picn
    cpi
    halfcl
    ax-mp
    #
    cA
    asincl
    #
    @1
    @5
    subneg
    sylancr
    @0
    @3
    @10
    @1
    cmin
    cA
    asinneg
    oveq2d
    @0
    @7
    cpi
    @1
    cmin
    co
    #
    @5
    caddc
    co
    @12
    @0
    cpi
    @1
    @5
    @14
    @0
    picn
    a1i
    @13
    @0
    @15
    a1i
    @16
    subsubd
    @17
    @1
    @5
    caddc
    cpi
    @1
    @1
    picn
    @15
    @15
    pidiv2halves
    subaddrii
    oveq1i
    syl6eq
    3eqtr4d
    @0
    @2
    cc
    wcel
    @8
    @4
    wceq
    cA
    negcl
    @2
    acosval
    syl
    @0
    @9
    @6
    cpi
    cmin
    cA
    acosval
    oveq2d
    3eqtr4d
end
