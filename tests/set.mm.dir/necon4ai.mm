include "wn.mm"
include "wceq.mm"
include "notnot.mm"
include "necon1bi.mm"
include "syl.mm"

theorem necon4ai
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon4ai.1: |- ( A =/= B -> -. ph )


  assert |- ( ph -> A = B )

  proof
    wph
    wph
    wn
    #
    wn
    cA
    cB
    wceq
    wph
    notnot
    @0
    cA
    cB
    necon4ai.1
    necon1bi
    syl
end
