include "imorri.mm"
include "ax-mp.mm"

theorem anmp
  let wph: wff ph
  let wps: wff ps
  assume anmp.min: |- ph
  assume anmp.maj: |- ( -. ph \/ ps )


  assert |- ps

  proof
    wph
    wps
    anmp.min
    wph
    wps
    anmp.maj
    imorri
    ax-mp
end
