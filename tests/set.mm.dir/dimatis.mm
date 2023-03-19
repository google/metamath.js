include "wa.mm"
include "wi.mm"
include "spi.mm"
include "adantl.mm"
include "simpl.mm"
include "jca.mm"
include "eximii.mm"

theorem dimatis
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume dimatis.maj: |- E. x ( ph /\ ps )
  assume dimatis.min: |- A. x ( ps -> ch )


  assert |- E. x ( ch /\ ph )

  proof
    wph
    wps
    wa
    #
    wch
    wph
    wa
    vx
    dimatis.maj
    @0
    wch
    wph
    wps
    wch
    wph
    wps
    wch
    wi
    vx
    dimatis.min
    spi
    adantl
    wph
    wps
    simpl
    jca
    eximii
end
