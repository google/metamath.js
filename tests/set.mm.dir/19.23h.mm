include "nf5i.mm"
include "19.23.mm"

theorem 19.23h
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.23h.1: |- ( ps -> A. x ps )


  assert |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )

  proof
    wph
    wps
    vx
    wps
    vx
    19.23h.1
    nf5i
    19.23
end
