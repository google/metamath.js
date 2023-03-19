include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wmo.mm"
include "wi.mm"
include "moanimv.mm"
include "mpbir.mm"
include "ovidig.mm"
include "ex.mm"

theorem ovidi
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cF: class F
  assume ovidi.2: |- ( ( x e. R /\ y e. S ) -> E* z ph )
  assume ovidi.3: |- F = { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S z
  assert |- ( ( x e. R /\ y e. S ) -> ( ph -> ( x F y ) = z ) )

  proof
    vx
    cv
    #
    cR
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    #
    wph
    @0
    @1
    cF
    co
    vz
    cv
    wceq
    @2
    wph
    wa
    #
    vx
    vy
    vz
    cF
    @3
    vz
    wmo
    @2
    wph
    vz
    wmo
    wi
    ovidi.2
    @2
    wph
    vz
    moanimv
    mpbir
    ovidi.3
    ovidig
    ex
end
