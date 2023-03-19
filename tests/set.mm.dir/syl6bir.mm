include "biimprd.mm"
include "syl6.mm"

theorem syl6bir
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6bir.1: |- ( ph -> ( ch <-> ps ) )
  assume syl6bir.2: |- ( ch -> th )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wch
    wps
    syl6bir.1
    biimprd
    syl6bir.2
    syl6
end
