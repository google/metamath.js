include "nfriOLD.mm"
include "nexdh.mm"

theorem nexdOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nexdOLD.1: |- nfOLD x ph
  assume nexdOLD.2: |- ( ph -> -. ps )


  assert |- ( ph -> -. E. x ps )

  proof
    wph
    wps
    vx
    wph
    vx
    nexdOLD.1
    nfriOLD
    nexdOLD.2
    nexdh
end
