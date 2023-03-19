include "wa.mm"
include "simprd.mm"

theorem simprrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simprrd.1: |- ( ph -> ( ps /\ ( ch /\ th ) ) )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    wth
    wa
    simprrd.1
    simprd
    simprd
end
