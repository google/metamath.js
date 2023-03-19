include "nf5i.mm"
include "bj-cbv3v2.mm"

theorem bj-cbv3hv2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbv3hv2.nf: |- ( ps -> A. x ps )
  assume bj-cbv3hv2.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  disjoint ph y
  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    bj-cbv3hv2.nf
    nf5i
    bj-cbv3hv2.1
    bj-cbv3v2
end
