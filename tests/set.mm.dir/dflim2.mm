include "wlim.mm"
include "word.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "wcel.mm"
include "df-lim.mm"
include "wa.mm"
include "ord0eln0.mm"
include "anbi1d.mm"
include "pm5.32i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "bitr4i.mm"

theorem dflim2
  let cA: class A


  assert |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A = U. A ) )

  proof
    cA
    wlim
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
    wceq
    #
    w3a
    #
    @0
    c0
    cA
    wcel
    #
    @2
    w3a
    #
    cA
    df-lim
    @0
    @4
    @2
    wa
    #
    wa
    @0
    @1
    @2
    wa
    #
    wa
    @5
    @3
    @0
    @6
    @7
    @0
    @4
    @1
    @2
    cA
    ord0eln0
    anbi1d
    pm5.32i
    @0
    @4
    @2
    3anass
    @0
    @1
    @2
    3anass
    3bitr4i
    bitr4i
end
