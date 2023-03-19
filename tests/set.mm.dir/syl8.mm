include "wi.mm"
include "a1i.mm"
include "syl6d.mm"

theorem syl8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
