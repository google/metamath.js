include "wa.mm"
include "wi.mm"
include "spi.mm"
include "anim1i.mm"
include "eximii.mm"

theorem disamis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume disamis.maj: |- E. x ( ph /\ ps )
  assume disamis.min: |- A. x ( ph -> ch )


  assert |- E. x ( ch /\ ps )

  proof
    wph
    wps
    wa
    wch
    wps
    wa
    vx
    disamis.maj
    wph
    wch
    wps
    wph
    wch
    wi
    vx
    disamis.min
    spi
    anim1i
    eximii
end
