include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "sylbir.mm"
include "con1i.mm"

theorem necon1bi
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon1bi.1: |- ( A =/= B -> ph )


  assert |- ( -. ph -> A = B )

  proof
    cA
    cB
    wceq
    #
    wph
    @0
    wn
    cA
    cB
    wne
    wph
    cA
    cB
    df-ne
    necon1bi.1
    sylbir
    con1i
end
