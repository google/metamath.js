include "wi.mm"
include "syl9r.mm"
include "imp.mm"

theorem sylan9r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume sylan9r.1: |- ( ph -> ( ps -> ch ) )
  assume sylan9r.2: |- ( th -> ( ch -> ta ) )


  assert |- ( ( th /\ ph ) -> ( ps -> ta ) )

  proof
    wth
    wph
    wps
    wta
    wi
    wph
    wps
    wch
    wth
    wta
    sylan9r.1
    sylan9r.2
    syl9r
    imp
end
