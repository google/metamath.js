include "nfv.mm"
include "cbvoprab12.mm"

theorem cbvoprab12v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume cbvoprab12v.1: |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint ph w
  disjoint ph v
  disjoint ps x
  disjoint ps y
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. w , v >. , z >. | ps }

  proof
    wph
    wps
    vx
    vy
    vz
    vw
    vv
    wph
    vw
    nfv
    wph
    vv
    nfv
    wps
    vx
    nfv
    wps
    vy
    nfv
    cbvoprab12v.1
    cbvoprab12
end
