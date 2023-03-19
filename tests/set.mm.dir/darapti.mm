include "wa.mm"
include "wi.mm"
include "spi.mm"
include "jca.mm"
include "eximii.mm"

theorem darapti
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume darapti.maj: |- A. x ( ph -> ps )
  assume darapti.min: |- A. x ( ph -> ch )
  assume darapti.e: |- E. x ph


  assert |- E. x ( ch /\ ps )

  proof
    wph
    wch
    wps
    wa
    vx
    darapti.e
    wph
    wch
    wps
    wph
    wch
    wi
    vx
    darapti.min
    spi
    wph
    wps
    wi
    vx
    darapti.maj
    spi
    jca
    eximii
end
