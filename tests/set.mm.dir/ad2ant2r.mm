include "wa.mm"
include "adantrr.mm"
include "adantlr.mm"

theorem ad2ant2r
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume ad2ant2.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ph /\ th ) /\ ( ps /\ ta ) ) -> ch )

  proof
    wph
    wps
    wta
    wa
    wch
    wth
    wph
    wps
    wch
    wta
    ad2ant2.1
    adantrr
    adantlr
end
