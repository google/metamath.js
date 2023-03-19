include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "ssexg.mm"
include "ancoms.mm"
include "ressress.mm"
include "syldan.mm"
include "simpr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem ressabs
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X


  assert |- ( ( A e. X /\ B C_ A ) -> ( ( W |`s A ) |`s B ) = ( W |`s B ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cW
    cA
    cress
    co
    cB
    cress
    co
    #
    cW
    cA
    cB
    cin
    #
    cress
    co
    #
    cW
    cB
    cress
    co
    @0
    @1
    cB
    cvv
    wcel
    #
    @3
    @5
    wceq
    @1
    @0
    @6
    cB
    cA
    cX
    ssexg
    ancoms
    cA
    cB
    cW
    cX
    cvv
    ressress
    syldan
    @2
    @4
    cB
    cW
    cress
    @2
    @1
    @4
    cB
    wceq
    @0
    @1
    simpr
    cB
    cA
    sseqin2
    sylib
    oveq2d
    eqtrd
end
