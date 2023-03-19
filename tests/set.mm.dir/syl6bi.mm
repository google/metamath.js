include "biimpd.mm"
include "syl6.mm"

theorem syl6bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl6bi.1: |- ( ph -> ( ps <-> ch ) )
  assume syl6bi.2: |- ( ch -> th )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    syl6bi.1
    biimpd
    syl6bi.2
    syl6
end
