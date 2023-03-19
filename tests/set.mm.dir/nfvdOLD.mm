include "wnfOLD.mm"
include "nfvOLD.mm"
include "a1i.mm"

theorem nfvdOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( ph -> nfOLD x ps )

  proof
    wps
    vx
    wnfOLD
    wph
    wps
    vx
    nfvOLD
    a1i
end
