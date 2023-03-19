include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "hashprb.mm"
include "bitr4i.mm"
include "prid1g.mm"
include "3ad2ant1.mm"
include "syl6eleqr.mm"
include "prid2g.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "3jca.mm"
include "sylbi.mm"

theorem hashprdifel
  let cA: class A
  let cB: class B
  let cS: class S
  assume hashprdifel.s: |- S = { A , B }


  assert |- ( ( # ` S ) = 2 -> ( A e. S /\ B e. S /\ A =/= B ) )

  proof
    cS
    chash
    cfv
    #
    c2
    wceq
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    @4
    w3a
    @1
    cA
    cB
    cpr
    #
    chash
    cfv
    #
    c2
    wceq
    @5
    @0
    @9
    c2
    cS
    @8
    chash
    hashprdifel.s
    fveq2i
    eqeq1i
    cA
    cB
    hashprb
    bitr4i
    @5
    @6
    @7
    @4
    @5
    cA
    @8
    cS
    @2
    @3
    cA
    @8
    wcel
    @4
    cA
    cB
    cvv
    prid1g
    3ad2ant1
    hashprdifel.s
    syl6eleqr
    @5
    cB
    @8
    cS
    @3
    @2
    cB
    @8
    wcel
    @4
    cA
    cB
    cvv
    prid2g
    3ad2ant2
    hashprdifel.s
    syl6eleqr
    @2
    @3
    @4
    simp3
    3jca
    sylbi
end
