include "wn.mm"
include "wa.mm"
include "wi.mm"
include "spi.mm"
include "nsyl3.mm"
include "ancli.mm"
include "eximii.mm"

theorem cesaro
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume cesaro.maj: |- A. x ( ph -> -. ps )
  assume cesaro.min: |- A. x ( ch -> ps )
  assume cesaro.e: |- E. x ch


  assert |- E. x ( ch /\ -. ph )

  proof
    wch
    wch
    wph
    wn
    #
    wa
    vx
    cesaro.e
    wch
    @0
    wph
    wps
    wch
    wph
    wps
    wn
    wi
    vx
    cesaro.maj
    spi
    wch
    wps
    wi
    vx
    cesaro.min
    spi
    nsyl3
    ancli
    eximii
end
