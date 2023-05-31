include "wi.mm"
include "a1i.mm"
include "sylcom.mm"

theorem syl6
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6.1: |- ( ph -> ( ps -> ch ) )
  assume syl6.2: |- ( ch -> th )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    syl6.1
    wch
    wth
    wi
    wps
    syl6.2
    a1i
    sylcom
end
