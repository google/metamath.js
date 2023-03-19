include "nfv.mm"
include "cbvopab1.mm"

theorem cbvopab1v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cbvopab1v.1: |- ( x = z -> ( ph <-> ps ) )

  disjoint x y
  disjoint y z
  disjoint ph z
  disjoint ps x
  assert |- { <. x , y >. | ph } = { <. z , y >. | ps }

  proof
    wph
    wps
    vx
    vy
    vz
    wph
    vz
    nfv
    wps
    vx
    nfv
    cbvopab1v.1
    cbvopab1
end
