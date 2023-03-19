include "wceq.mm"
include "ex.mm"
include "wne.mm"
include "pm2.61dne.mm"

theorem pm2.61dane
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume pm2.61dane.1: |- ( ( ph /\ A = B ) -> ps )
  assume pm2.61dane.2: |- ( ( ph /\ A =/= B ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    cA
    cB
    wph
    cA
    cB
    wceq
    wps
    pm2.61dane.1
    ex
    wph
    cA
    cB
    wne
    wps
    pm2.61dane.2
    ex
    pm2.61dne
end
