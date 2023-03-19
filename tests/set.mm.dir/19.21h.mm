include "nf5i.mm"
include "19.21.mm"

theorem 19.21h
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.21h.1: |- ( ph -> A. x ph )


  assert |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) )

  proof
    wph
    wps
    vx
    wph
    vx
    19.21h.1
    nf5i
    19.21
end
