include "wi.mm"
include "syl9.mm"
include "imp.mm"

theorem sylan9
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume sylan9.1: |- ( ph -> ( ps -> ch ) )
  assume sylan9.2: |- ( th -> ( ch -> ta ) )


  assert |- ( ( ph /\ th ) -> ( ps -> ta ) )

  proof
    wph
    wth
    wps
    wta
    wi
    wph
    wps
    wch
    wth
    wta
    sylan9.1
    sylan9.2
    syl9
    imp
end
