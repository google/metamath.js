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
include "sylan.mm"
include "ococ.mm"
include "ineq1d.mm"
include "adantr.mm"
include "eqtrd.mm"

theorem chdmj2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( ( _|_ ` A ) vH B ) ) = ( A i^i ( _|_ ` B ) ) )

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
    cA
    cort
    cfv
    #
    cB
    chj
    co
    cort
    cfv
    #
    @2
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cin
    #
    cA
    @5
    cin
    #
    @0
    @2
    cch
    wcel
    @1
    @3
    @6
    wceq
    cA
    choccl
    @2
    cB
    chdmj1
    sylan
    @0
    @6
    @7
    wceq
    @1
    @0
    @4
    cA
    @5
    cA
    ococ
    ineq1d
    adantr
    eqtrd
end
