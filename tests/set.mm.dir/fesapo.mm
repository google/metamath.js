include "wn.mm"
include "wa.mm"
include "wi.mm"
include "spi.mm"
include "con2i.mm"
include "jca.mm"
include "eximii.mm"

theorem fesapo
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume fesapo.maj: |- A. x ( ph -> -. ps )
  assume fesapo.min: |- A. x ( ps -> ch )
  assume fesapo.e: |- E. x ps


  assert |- E. x ( ch /\ -. ph )

  proof
    wps
    wch
    wph
    wn
    #
    wa
    vx
    fesapo.e
    wps
    wch
    @0
    wps
    wch
    wi
    vx
    fesapo.min
    spi
    wph
    wps
    wph
    wps
    wn
    wi
    vx
    fesapo.maj
    spi
    con2i
    jca
    eximii
end
