include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "choccl.mm"
include "chdmm1.mm"
include "sylan.mm"
include "ococ.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem chdmm2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( ( _|_ ` A ) i^i B ) ) = ( A vH ( _|_ ` B ) ) )

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
    #
    cB
    cin
    cort
    cfv
    #
    @3
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    chj
    co
    #
    cA
    @6
    chj
    co
    @0
    @3
    cch
    wcel
    @1
    @4
    @7
    wceq
    cA
    choccl
    @3
    cB
    chdmm1
    sylan
    @2
    @5
    cA
    @6
    chj
    @0
    @5
    cA
    wceq
    @1
    cA
    ococ
    adantr
    oveq1d
    eqtrd
end
