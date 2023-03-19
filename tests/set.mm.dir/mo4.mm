include "nfv.mm"
include "mo4f.mm"

theorem mo4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume mo4.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) )

  proof
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    mo4.1
    mo4f
end
