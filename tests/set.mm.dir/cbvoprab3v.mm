include "nfv.mm"
include "cbvoprab3.mm"

theorem cbvoprab3v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbvoprab3v.1: |- ( z = w -> ( ph <-> ps ) )

  disjoint x z
  disjoint w x
  disjoint w z
  disjoint y z
  disjoint w y
  disjoint ph w
  disjoint ps z
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , w >. | ps }

  proof
    wph
    wps
    vx
    vy
    vz
    vw
    wph
    vw
    nfv
    wps
    vz
    nfv
    cbvoprab3v.1
    cbvoprab3
end
