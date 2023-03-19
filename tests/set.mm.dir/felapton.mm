include "wn.mm"
include "wa.mm"
include "wi.mm"
include "spi.mm"
include "jca.mm"
include "eximii.mm"

theorem felapton
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume felapton.maj: |- A. x ( ph -> -. ps )
  assume felapton.min: |- A. x ( ph -> ch )
  assume felapton.e: |- E. x ph


  assert |- E. x ( ch /\ -. ps )

  proof
    wph
    wch
    wps
    wn
    #
    wa
    vx
    felapton.e
    wph
    wch
    @0
    wph
    wch
    wi
    vx
    felapton.min
    spi
    wph
    @0
    wi
    vx
    felapton.maj
    spi
    jca
    eximii
end
