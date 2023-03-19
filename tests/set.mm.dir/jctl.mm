include "id.mm"
include "jctil.mm"

theorem jctl
  let wph: wff ph
  let wps: wff ps
  assume jctl.1: |- ps


  assert |- ( ph -> ( ps /\ ph ) )

  proof
    wph
    wph
    wps
    wph
    id
    jctl.1
    jctil
end
