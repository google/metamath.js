include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "sylibr.mm"

theorem neqned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume neqned.1: |- ( ph -> -. A = B )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cA
    cB
    wceq
    wn
    cA
    cB
    wne
    neqned.1
    cA
    cB
    df-ne
    sylibr
end
