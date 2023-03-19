include "cr.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "c2.mm"
include "cexp.mm"
include "cjre.mm"
include "oveq2d.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "absvalsq.mm"
include "syl.mm"
include "sqvald.mm"
include "3eqtr4d.mm"

theorem absresq
  let cA: class A


  assert |- ( A e. RR -> ( ( abs ` A ) ^ 2 ) = ( A ^ 2 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    cA
    cA
    cmul
    co
    cA
    cabs
    cfv
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    @0
    @1
    cA
    cA
    cmul
    cA
    cjre
    oveq2d
    @0
    cA
    cc
    wcel
    @3
    @2
    wceq
    cA
    recn
    #
    cA
    absvalsq
    syl
    @0
    cA
    @4
    sqvald
    3eqtr4d
end
