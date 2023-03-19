include "wceq.mm"
include "neneqd.mm"
include "pm2.21dd.mm"

theorem pm2.21ddne
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume pm2.21ddne.1: |- ( ph -> A = B )
  assume pm2.21ddne.2: |- ( ph -> A =/= B )


  assert |- ( ph -> ps )

  proof
    wph
    cA
    cB
    wceq
    wps
    pm2.21ddne.1
    wph
    cA
    cB
    pm2.21ddne.2
    neneqd
    pm2.21dd
end
