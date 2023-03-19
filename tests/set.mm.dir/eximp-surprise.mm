include "wi.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "exbii.mm"

theorem eximp-surprise
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vk: setvar k


  assert |- ( E. x ( ph -> ps ) <-> E. x ( -. ph \/ ps ) )

  proof
    wph
    wps
    wi
    wph
    wn
    wps
    wo
    vx
    wph
    wps
    imor
    exbii
end
