include "a1d.mm"
include "syl6c.mm"

theorem syl6ci
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl6ci.1: |- ( ph -> ( ps -> ch ) )
  assume syl6ci.2: |- ( ph -> th )
  assume syl6ci.3: |- ( ch -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wch
    wth
    wta
    syl6ci.1
    wph
    wth
    wps
    syl6ci.2
    a1d
    syl6ci.3
    syl6c
end
