include "id.mm"
include "jctir.mm"

theorem jctr
  let wph: wff ph
  let wps: wff ps
  assume jctl.1: |- ps


  assert |- ( ph -> ( ph /\ ps ) )

  proof
    wph
    wph
    wps
    wph
    id
    jctl.1
    jctir
end
