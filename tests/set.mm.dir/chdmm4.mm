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
include "chdmm2.mm"
include "sylan2.mm"
include "ococ.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem chdmm4
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( ( _|_ ` A ) i^i ( _|_ ` B ) ) ) = ( A vH B ) )

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
    cin
    cort
    cfv
    #
    cA
    @3
    cort
    cfv
    #
    chj
    co
    #
    cA
    cB
    chj
    co
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
    chdmm2
    sylan2
    @2
    @5
    cB
    cA
    chj
    @1
    @5
    cB
    wceq
    @0
    cB
    ococ
    adantl
    oveq2d
    eqtrd
end
