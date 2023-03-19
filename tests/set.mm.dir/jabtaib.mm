include "wa.mm"
include "wi.mm"
include "pm3.4.mm"
include "ax-mp.mm"

theorem jabtaib
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume jabtaib.1: |- ( ph /\ ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wa
    wph
    wps
    wi
    jabtaib.1
    wph
    wps
    pm3.4
    ax-mp
end
