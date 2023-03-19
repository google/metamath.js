include "biimpi.mm"
include "syl5.mm"

theorem syl5bi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
