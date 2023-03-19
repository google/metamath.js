include "wex.mm"
include "weq.mm"
include "wa.mm"
include "2exbidv.mm"
include "cbvex2v.mm"
include "2exbii.mm"
include "bitri.mm"

theorem cbvex4v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cbvex4v.vf: setvar f
  let cbvex4v.vg: setvar g
  assume cbvex4v.1: |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) )
  assume cbvex4v.2: |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) )

  disjoint w z
  disjoint ch w
  disjoint ch z
  disjoint u v
  disjoint ph u
  disjoint ph v
  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint f g
  disjoint f ps
  disjoint g ps
  disjoint f w
  disjoint g z
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint u x
  disjoint w x
  disjoint x z
  disjoint v y
  disjoint w y
  disjoint y z
  assert |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch )

  proof
    wph
    vw
    wex
    vz
    wex
    #
    vy
    wex
    vx
    wex
    wps
    vw
    wex
    vz
    wex
    #
    vu
    wex
    vv
    wex
    wch
    cbvex4v.vg
    wex
    cbvex4v.vf
    wex
    #
    vu
    wex
    vv
    wex
    @0
    @1
    vx
    vy
    vv
    vu
    vx
    vv
    weq
    vy
    vu
    weq
    wa
    wph
    wps
    vz
    vw
    cbvex4v.1
    2exbidv
    cbvex2v
    @1
    @2
    vv
    vu
    wps
    wch
    vz
    vw
    cbvex4v.vf
    cbvex4v.vg
    cbvex4v.2
    cbvex2v
    2exbii
    bitri
end
