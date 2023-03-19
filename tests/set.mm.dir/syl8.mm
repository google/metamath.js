include "wi.mm"
include "a1i.mm"
include "syl6d.mm"

theorem syl8
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl8.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume syl8.2: |- ( th -> ta )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    syl8.1
    wth
    wta
    wi
    wph
    syl8.2
    a1i
    syl6d
end
