include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "mul2neg.mm"
include "anidms.mm"
include "negcl.mm"
include "sqval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem sqneg
  let cA: class A


  assert |- ( A e. CC -> ( -u A ^ 2 ) = ( A ^ 2 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    @1
    cmul
    co
    #
    cA
    cA
    cmul
    co
    #
    @1
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    @0
    @2
    @3
    wceq
    cA
    cA
    mul2neg
    anidms
    @0
    @1
    cc
    wcel
    @4
    @2
    wceq
    cA
    negcl
    @1
    sqval
    syl
    cA
    sqval
    3eqtr4d
end
