include "wnf.mm"
include "nfv.mm"
include "a1i.mm"

theorem nfvd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( ph -> F/ x ps )

  proof
    wps
    vx
    wnf
    wph
    wps
    vx
    nfv
    a1i
end
