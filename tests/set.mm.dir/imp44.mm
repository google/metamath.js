include "wa.mm"
include "imp4c.mm"
include "imp.mm"

theorem imp44
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume imp4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta )

  proof
    wph
    wps
    wch
    wa
    wth
    wa
    wta
    wph
    wps
    wch
    wth
    wta
    imp4.1
    imp4c
    imp
end
