include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "nne.mm"
include "syl5bi.mm"
include "pm2.61d.mm"

theorem pm2.61dne
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume pm2.61dne.1: |- ( ph -> ( A = B -> ps ) )
  assume pm2.61dne.2: |- ( ph -> ( A =/= B -> ps ) )


  assert |- ( ph -> ps )

  proof
    wph
    cA
    cB
    wne
    #
    wps
    pm2.61dne.2
    @0
    wn
    cA
    cB
    wceq
    wph
    wps
    cA
    cB
    nne
    pm2.61dne.1
    syl5bi
    pm2.61d
end
