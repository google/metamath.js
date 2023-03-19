include "wpss.mm"
include "wne.mm"
include "pssne.mm"
include "syl.mm"

theorem pssned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume pssssd.1: |- ( ph -> A C. B )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cA
    cB
    wpss
    cA
    cB
    wne
    pssssd.1
    cA
    cB
    pssne
    syl
end
