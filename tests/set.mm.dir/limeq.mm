include "wceq.mm"
include "word.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "w3a.mm"
include "wlim.mm"
include "ordeq.mm"
include "neeq1.mm"
include "id.mm"
include "unieq.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "df-lim.mm"
include "3bitr4g.mm"

theorem limeq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( Lim A <-> Lim B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    word
    #
    cA
    c0
    wne
    #
    cA
    cA
    cuni
    #
    wceq
    #
    w3a
    cB
    word
    #
    cB
    c0
    wne
    #
    cB
    cB
    cuni
    #
    wceq
    #
    w3a
    cA
    wlim
    cB
    wlim
    @0
    @1
    @5
    @2
    @6
    @4
    @8
    cA
    cB
    ordeq
    cA
    cB
    c0
    neeq1
    @0
    cA
    cB
    @3
    @7
    @0
    id
    cA
    cB
    unieq
    eqeq12d
    3anbi123d
    cA
    df-lim
    cB
    df-lim
    3bitr4g
end
