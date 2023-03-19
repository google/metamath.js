include "nfv.mm"
include "cbval2.mm"

theorem cbval2vOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbval2v.1: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint w x
  disjoint y z
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
    cbval2v.1
    cbval2
end
