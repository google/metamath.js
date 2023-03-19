include "nfv.mm"
include "cbvex2.mm"

theorem cbvex2vOLD
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
  assert |- ( E. x E. y ph <-> E. z E. w ps )

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
    cbvex2
end
