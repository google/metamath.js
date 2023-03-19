include "wa.mm"
include "wn.mm"
include "simpr.mm"
include "wi.mm"
include "spi.mm"
include "con2i.mm"
include "adantr.mm"
include "jca.mm"
include "eximii.mm"

theorem fresison
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume fresison.maj: |- A. x ( ph -> -. ps )
  assume fresison.min: |- E. x ( ps /\ ch )


  assert |- E. x ( ch /\ -. ph )

  proof
    wps
    wch
    wa
    #
    wch
    wph
    wn
    #
    wa
    vx
    fresison.min
    @0
    wch
    @1
    wps
    wch
    simpr
    wps
    @1
    wch
    wph
    wps
    wph
    wps
    wn
    wi
    vx
    fresison.maj
    spi
    con2i
    adantr
    jca
    eximii
end
