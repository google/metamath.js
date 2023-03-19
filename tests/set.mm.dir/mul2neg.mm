include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "negcl.mm"
include "mulneg12.mm"
include "sylan2.mm"
include "negneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem mul2neg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( -u A x. -u B ) = ( A x. B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cneg
    cB
    cneg
    #
    cmul
    co
    #
    cA
    @3
    cneg
    #
    cmul
    co
    #
    cA
    cB
    cmul
    co
    @1
    @0
    @3
    cc
    wcel
    @4
    @6
    wceq
    cB
    negcl
    cA
    @3
    mulneg12
    sylan2
    @2
    @5
    cB
    cA
    cmul
    @1
    @5
    cB
    wceq
    @0
    cB
    negneg
    adantl
    oveq2d
    eqtrd
end
