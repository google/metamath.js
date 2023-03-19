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
include "chdmj1.mm"
include "sylan2.mm"
include "ococ.mm"
include "adantl.mm"
include "ineq2d.mm"
include "eqtrd.mm"

theorem chdmj3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( A vH ( _|_ ` B ) ) ) = ( ( _|_ ` A ) i^i B ) )

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
    cort
    cfv
    #
    @3
    cort
    cfv
    #
    cin
    #
    @5
    cB
    cin
    @1
    @0
    @3
    cch
    wcel
    @4
    @7
    wceq
    cB
    choccl
    cA
    @3
    chdmj1
    sylan2
    @2
    @6
    cB
    @5
    @1
    @6
    cB
    wceq
    @0
    cB
    ococ
    adantl
    ineq2d
    eqtrd
end
