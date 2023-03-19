include "wi.mm"
include "a1d.mm"
include "syldd.mm"

theorem syl6d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl6d.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume syl6d.2: |- ( ph -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    syl6d.1
    wph
    wth
    wta
    wi
    wps
    syl6d.2
    a1d
    syldd
end
