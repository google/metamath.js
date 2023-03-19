include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "divneg.mm"
include "wceq.mm"
include "negcl.mm"
include "div2neg.mm"
include "syl3an1.mm"
include "negneg.mm"
include "3ad2ant1.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"

theorem divneg2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> -u ( A / B ) = ( A / -u B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    cneg
    cA
    cneg
    #
    cB
    cdiv
    co
    #
    @4
    cneg
    #
    cB
    cneg
    #
    cdiv
    co
    #
    cA
    @7
    cdiv
    co
    cA
    cB
    divneg
    @0
    @4
    cc
    wcel
    @1
    @2
    @8
    @5
    wceq
    cA
    negcl
    @4
    cB
    div2neg
    syl3an1
    @3
    @6
    cA
    @7
    cdiv
    @0
    @1
    @6
    cA
    wceq
    @2
    cA
    negneg
    3ad2ant1
    oveq1d
    3eqtr2d
end
