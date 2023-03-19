include "wi.mm"
include "imim2.mm"
include "syl6c.mm"

theorem syldd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
