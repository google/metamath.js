include "wpss.mm"
include "wss.mm"
include "pssss.mm"
include "syl.mm"

theorem pssssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume pssssd.1: |- ( ph -> A C. B )


  assert |- ( ph -> A C_ B )

  proof
    wph
    cA
    cB
    wpss
    cA
    cB
    wss
    pssssd.1
    cA
    cB
    pssss
    syl
end
