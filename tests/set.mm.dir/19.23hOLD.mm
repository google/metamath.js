include "nfiOLD.mm"
include "19.23OLD.mm"

theorem 19.23hOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.23hOLD.1: |- ( ps -> A. x ps )


  assert |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )

  proof
    wph
    wps
    vx
    wps
    vx
    19.23hOLD.1
    nfiOLD
    19.23OLD
end
