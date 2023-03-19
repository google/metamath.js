include "nfv.mm"
include "cbvopab.mm"

theorem cbvopabv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbvopabv.1: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint ps x
  disjoint ps y
  assert |- { <. x , y >. | ph } = { <. z , w >. | ps }

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
    cbvopabv.1
    cbvopab
end
