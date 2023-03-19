include "ax-5.mm"
include "nexdh.mm"

theorem nexdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nexdv.1: |- ( ph -> -. ps )

  disjoint ph x
  assert |- ( ph -> -. E. x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    ax-5
    nexdv.1
    nexdh
end
