include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "wne.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wb.mm"
include "atsseq.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ancoms.mm"
include "necon3bbid.mm"
include "cch.mm"
include "atelch.mm"
include "atnssm0.mm"
include "sylan.mm"
include "bitr3d.mm"

theorem atnemeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. HAtoms /\ B e. HAtoms ) -> ( A =/= B <-> ( A i^i B ) = 0H ) )

  proof
    cA
    cat
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    #
    cB
    cA
    wss
    #
    wn
    #
    cA
    cB
    wne
    cA
    cB
    cin
    c0h
    wceq
    #
    @2
    @3
    cA
    cB
    @1
    @0
    @3
    cA
    cB
    wceq
    #
    wb
    @1
    @0
    wa
    @3
    cB
    cA
    wceq
    @6
    cB
    cA
    atsseq
    cB
    cA
    eqcom
    syl6bb
    ancoms
    necon3bbid
    @0
    cA
    cch
    wcel
    @1
    @4
    @5
    wb
    cA
    atelch
    cA
    cB
    atnssm0
    sylan
    bitr3d
end
