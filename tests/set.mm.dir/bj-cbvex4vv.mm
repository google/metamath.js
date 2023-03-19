include "wex.mm"
include "weq.mm"
include "wa.mm"
include "2exbidv.mm"
include "bj-cbvex2vv.mm"
include "2exbii.mm"
include "bitri.mm"

theorem bj-cbvex4vv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  assume bj-cbvex4vv.1: |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) )
  assume bj-cbvex4vv.2: |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) )

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
  disjoint f z
  disjoint g z
  disjoint f w
  disjoint g w
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint x z
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
    vg
    wex
    vf
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
    bj-cbvex4vv.1
    2exbidv
    bj-cbvex2vv
    @1
    @2
    vv
    vu
    wps
    wch
    vz
    vw
    vf
    vg
    bj-cbvex4vv.2
    bj-cbvex2vv
    2exbii
    bitri
end
