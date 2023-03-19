include "wa.mm"
include "wi.mm"
include "spi.mm"
include "syl.mm"
include "ancri.mm"
include "eximii.mm"

theorem bamalip
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bamalip.maj: |- A. x ( ph -> ps )
  assume bamalip.min: |- A. x ( ps -> ch )
  assume bamalip.e: |- E. x ph


  assert |- E. x ( ch /\ ph )

  proof
    wph
    wch
    wph
    wa
    vx
    bamalip.e
    wph
    wch
    wph
    wps
    wch
    wph
    wps
    wi
    vx
    bamalip.maj
    spi
    wps
    wch
    wi
    vx
    bamalip.min
    spi
    syl
    ancri
    eximii
end
