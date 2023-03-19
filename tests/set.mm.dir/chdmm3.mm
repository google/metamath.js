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
include "sylan2.mm"
include "ococ.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem chdmm3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( A i^i ( _|_ ` B ) ) ) = ( ( _|_ ` A ) vH B ) )

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
    cin
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
    chj
    co
    #
    @5
    cB
    chj
    co
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
    chdmm1
    sylan2
    @2
    @6
    cB
    @5
    chj
    @1
    @6
    cB
    wceq
    @0
    cB
    ococ
    adantl
    oveq2d
    eqtrd
end
