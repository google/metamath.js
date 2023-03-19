include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "simpl.mm"
include "chjcl.mm"
include "chub1.mm"
include "pjoml2.mm"
include "syl3anc.mm"

theorem pjoml5
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A vH ( ( _|_ ` A ) i^i ( A vH B ) ) ) = ( A vH B ) )

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
    @0
    cA
    cB
    chj
    co
    #
    cch
    wcel
    cA
    @2
    wss
    cA
    cA
    cort
    cfv
    @2
    cin
    chj
    co
    @2
    wceq
    @0
    @1
    simpl
    cA
    cB
    chjcl
    cA
    cB
    chub1
    cA
    @2
    pjoml2
    syl3anc
end
