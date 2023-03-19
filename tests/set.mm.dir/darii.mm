include "wa.mm"
include "wi.mm"
include "spi.mm"
include "anim2i.mm"
include "eximii.mm"

theorem darii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume darii.maj: |- A. x ( ph -> ps )
  assume darii.min: |- E. x ( ch /\ ph )


  assert |- E. x ( ch /\ ps )

  proof
    wch
    wph
    wa
    wch
    wps
    wa
    vx
    darii.min
    wph
    wps
    wch
    wph
    wps
    wi
    vx
    darii.maj
    spi
    anim2i
    eximii
end
