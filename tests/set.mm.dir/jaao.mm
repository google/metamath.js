include "wa.mm"
include "wi.mm"
include "adantr.mm"
include "adantl.mm"
include "jaod.mm"

theorem jaao
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume jaao.1: |- ( ph -> ( ps -> ch ) )
  assume jaao.2: |- ( th -> ( ta -> ch ) )


  assert |- ( ( ph /\ th ) -> ( ( ps \/ ta ) -> ch ) )

  proof
    wph
    wth
    wa
    wps
    wch
    wta
    wph
    wps
    wch
    wi
    wth
    jaao.1
    adantr
    wth
    wta
    wch
    wi
    wph
    jaao.2
    adantl
    jaod
end
