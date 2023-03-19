include "nfv.mm"
include "bj-cbval2v.mm"

theorem bj-cbval2vv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume bj-cbval2vv.1: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  assert |- ( A. x A. y ph <-> A. z A. w ps )

  proof
    wph
    wps
    vx
    vy
    vz
    vw
    wph
    vz
    nfv
    wph
    vw
    nfv
    wps
    vx
    nfv
    wps
    vy
    nfv
    bj-cbval2vv.1
    bj-cbval2v
end
