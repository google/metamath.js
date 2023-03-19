include "wa.mm"
include "imp4d.mm"
include "imp.mm"

theorem imp45
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume imp4.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wa
    wa
    wta
    wph
    wps
    wch
    wth
    wta
    imp4.1
    imp4d
    imp
end
