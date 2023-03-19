include "wreu.mm"
include "wrmo.mm"
include "wi.mm"
include "wral.mm"
include "reurmo.mm"
include "rmoim.mm"
include "syl5.mm"

theorem reuimrmo
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vk: setvar k


  assert |- ( A. x e. A ( ph -> ps ) -> ( E! x e. A ps -> E* x e. A ph ) )

  proof
    wps
    vx
    cA
    wreu
    wps
    vx
    cA
    wrmo
    wph
    wps
    wi
    vx
    cA
    wral
    wph
    vx
    cA
    wrmo
    wps
    vx
    cA
    reurmo
    wph
    wps
    vx
    cA
    rmoim
    syl5
end
