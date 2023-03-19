include "wa.mm"
include "wi.mm"
include "barbara.mm"
include "spi.mm"
include "ancli.mm"
include "eximii.mm"

theorem barbari
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume barbari.maj: |- A. x ( ph -> ps )
  assume barbari.min: |- A. x ( ch -> ph )
  assume barbari.e: |- E. x ch


  assert |- E. x ( ch /\ ps )

  proof
    wch
    wch
    wps
    wa
    vx
    barbari.e
    wch
    wps
    wch
    wps
    wi
    vx
    wph
    wps
    wch
    vx
    barbari.maj
    barbari.min
    barbara
    spi
    ancli
    eximii
end
