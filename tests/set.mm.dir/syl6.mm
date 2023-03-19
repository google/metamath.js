include "wi.mm"
include "a1i.mm"
include "sylcom.mm"

theorem syl6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
