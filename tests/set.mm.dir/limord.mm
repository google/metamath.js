include "wlim.mm"
include "word.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wceq.mm"
include "df-lim.mm"
include "simp1bi.mm"

theorem limord
  let cA: class A


  assert |- ( Lim A -> Ord A )

  proof
    cA
    wlim
    cA
    word
    cA
    c0
    wne
    cA
    cA
    cuni
    wceq
    cA
    df-lim
    simp1bi
end
