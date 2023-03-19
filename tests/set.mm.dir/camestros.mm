include "wn.mm"
include "wa.mm"
include "wi.mm"
include "spi.mm"
include "nsyl.mm"
include "ancli.mm"
include "eximii.mm"

theorem camestros
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume camestros.maj: |- A. x ( ph -> ps )
  assume camestros.min: |- A. x ( ch -> -. ps )
  assume camestros.e: |- E. x ch


  assert |- E. x ( ch /\ -. ph )

  proof
    wch
    wch
    wph
    wn
    #
    wa
    vx
    camestros.e
    wch
    @0
    wch
    wps
    wph
    wch
    wps
    wn
    wi
    vx
    camestros.min
    spi
    wph
    wps
    wi
    vx
    camestros.maj
    spi
    nsyl
    ancli
    eximii
end
