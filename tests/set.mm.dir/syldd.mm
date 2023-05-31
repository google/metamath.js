include "wi.mm"
include "imim2.mm"
include "syl6c.mm"

theorem syldd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syldd.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume syldd.2: |- ( ph -> ( ps -> ( th -> ta ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wth
    wta
    wi
    wch
    wth
    wi
    wch
    wta
    wi
    syldd.2
    syldd.1
    wth
    wta
    wch
    imim2
    syl6c
end
