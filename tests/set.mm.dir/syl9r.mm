include "wi.mm"
include "syl9.mm"
include "com12.mm"

theorem syl9r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl9r.1: |- ( ph -> ( ps -> ch ) )
  assume syl9r.2: |- ( th -> ( ch -> ta ) )


  assert |- ( th -> ( ph -> ( ps -> ta ) ) )

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
    syl9r.1
    syl9r.2
    syl9
    com12
end
