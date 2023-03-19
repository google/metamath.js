include "wa.mm"
include "ancom.mm"
include "syl6bb.mm"

theorem biancomd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume biancomd.1: |- ( ph -> ( ps <-> ( th /\ ch ) ) )


  assert |- ( ph -> ( ps <-> ( ch /\ th ) ) )

  proof
    wph
    wps
    wth
    wch
    wa
    wch
    wth
    wa
    biancomd.1
    wth
    wch
    ancom
    syl6bb
end
