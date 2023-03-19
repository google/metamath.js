include "wi.mm"
include "a1i.mm"
include "syl5d.mm"

theorem syl7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl7.1: |- ( ph -> ps )
  assume syl7.2: |- ( ch -> ( th -> ( ps -> ta ) ) )


  assert |- ( ch -> ( th -> ( ph -> ta ) ) )

  proof
    wch
    wph
    wps
    wth
    wta
    wph
    wps
    wi
    wch
    syl7.1
    a1i
    syl7.2
    syl5d
end
