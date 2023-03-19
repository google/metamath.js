include "wa.mm"
include "simprd.mm"
include "simpld.mm"

theorem simprld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume simprld.1: |- ( ph -> ( ps /\ ( ch /\ th ) ) )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wth
    wph
    wps
    wch
    wth
    wa
    simprld.1
    simprd
    simpld
end
