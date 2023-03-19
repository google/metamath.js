include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "df-nel.mm"
include "pm2.24.mm"
include "syl5bi.mm"

theorem elnelall
  let wph: wff ph
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ( A e/ B -> ph ) )

  proof
    cA
    cB
    wnel
    cA
    cB
    wcel
    #
    wn
    @0
    wph
    cA
    cB
    df-nel
    @0
    wph
    pm2.24
    syl5bi
end
