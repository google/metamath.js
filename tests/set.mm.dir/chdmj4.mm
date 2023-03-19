include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "choccl.mm"
include "chdmj2.mm"
include "sylan2.mm"
include "ococ.mm"
include "adantl.mm"
include "ineq2d.mm"
include "eqtrd.mm"

theorem chdmj4
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( ( _|_ ` A ) vH ( _|_ ` B ) ) ) = ( A i^i B ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cort
    cfv
    cB
    cort
    cfv
    #
    chj
    co
    cort
    cfv
    #
    cA
    @3
    cort
    cfv
    #
    cin
    #
    cA
    cB
    cin
    @1
    @0
    @3
    cch
    wcel
    @4
    @6
    wceq
    cB
    choccl
    cA
    @3
    chdmj2
    sylan2
    @2
    @5
    cB
    cA
    @1
    @5
    cB
    wceq
    @0
    cB
    ococ
    adantl
    ineq2d
    eqtrd
end
