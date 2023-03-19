include "nf5ri.mm"
include "nexdh.mm"

theorem nexd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nexd.1: |- F/ x ph
  assume nexd.2: |- ( ph -> -. ps )


  assert |- ( ph -> -. E. x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    nexd.1
    nf5ri
    nexd.2
    nexdh
end
