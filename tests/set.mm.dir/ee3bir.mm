include "biimpri.mm"
include "syl8.mm"

theorem ee3bir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee3bir.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee3bir.2: |- ( ta <-> th )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    ee3bir.1
    wta
    wth
    ee3bir.2
    biimpri
    syl8
end
