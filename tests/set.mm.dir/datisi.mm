include "wa.mm"
include "simpr.mm"
include "wi.mm"
include "spi.mm"
include "adantr.mm"
include "jca.mm"
include "eximii.mm"

theorem datisi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume datisi.maj: |- A. x ( ph -> ps )
  assume datisi.min: |- E. x ( ph /\ ch )


  assert |- E. x ( ch /\ ps )

  proof
    wph
    wch
    wa
    #
    wch
    wps
    wa
    vx
    datisi.min
    @0
    wch
    wps
    wph
    wch
    simpr
    wph
    wps
    wch
    wph
    wps
    wi
    vx
    datisi.maj
    spi
    adantr
    jca
    eximii
end
