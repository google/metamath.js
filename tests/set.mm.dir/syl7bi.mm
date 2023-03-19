include "biimpi.mm"
include "syl7.mm"

theorem syl7bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl7bi.1: |- ( ph <-> ps )
  assume syl7bi.2: |- ( ch -> ( th -> ( ps -> ta ) ) )


  assert |- ( ch -> ( th -> ( ph -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    syl7bi.1
    biimpi
    syl7bi.2
    syl7
end
