include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "expneg.mm"
include "mpan2.mm"
include "exp1.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem expn1
  let cA: class A


  assert |- ( A e. CC -> ( A ^ -u 1 ) = ( 1 / A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    cneg
    cexp
    co
    #
    c1
    cA
    c1
    cexp
    co
    #
    cdiv
    co
    #
    c1
    cA
    cdiv
    co
    @0
    c1
    cn0
    wcel
    @1
    @3
    wceq
    1nn0
    cA
    c1
    expneg
    mpan2
    @0
    @2
    cA
    c1
    cdiv
    cA
    exp1
    oveq2d
    eqtrd
end
