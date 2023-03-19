include "biimpi.mm"
include "syl5.mm"

theorem syl5bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5bi.1: |- ( ph <-> ps )
  assume syl5bi.2: |- ( ch -> ( ps -> th ) )


  assert |- ( ch -> ( ph -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    syl5bi.1
    biimpi
    syl5bi.2
    syl5
end
