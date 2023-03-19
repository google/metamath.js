include "biimpi.mm"
include "syl8.mm"

theorem syl8ib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl8ib.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume syl8ib.2: |- ( th <-> ta )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    syl8ib.1
    wth
    wta
    syl8ib.2
    biimpi
    syl8
end
