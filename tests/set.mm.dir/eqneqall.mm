include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "pm2.24.mm"
include "syl5bi.mm"

theorem eqneqall
  let wph: wff ph
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( A =/= B -> ph ) )

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    #
    wn
    @0
    wph
    cA
    cB
    df-ne
    @0
    wph
    pm2.24
    syl5bi
end
