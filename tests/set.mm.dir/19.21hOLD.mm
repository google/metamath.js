include "nfiOLD.mm"
include "19.21OLD.mm"

theorem 19.21hOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.21hOLD.1: |- ( ph -> A. x ph )


  assert |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) )

  proof
    wph
    wps
    vx
    wph
    vx
    19.21hOLD.1
    nfiOLD
    19.21OLD
end
