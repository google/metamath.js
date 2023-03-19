include "cxp.mm"
include "cdm.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "opelxp.mm"
include "cafv.mm"
include "caov.mm"
include "df-aov.mm"
include "syl5eqelr.mm"
include "afvvdm.mm"
include "syl.mm"
include "sylbi.mm"
include "relssi.mm"

theorem aoprssdm
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let vk: setvar k
  assume aoprssdm.1: |- ( ( x e. S /\ y e. S ) -> (( x F y )) e. S )

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint k x
  assert |- ( S X. S ) C_ dom F

  proof
    vx
    vy
    cS
    cS
    cxp
    #
    cF
    cdm
    #
    cS
    cS
    relxp
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    @2
    cS
    wcel
    @3
    cS
    wcel
    wa
    #
    @4
    @1
    wcel
    #
    @2
    @3
    cS
    cS
    opelxp
    @5
    @4
    cF
    cafv
    #
    cS
    wcel
    @6
    @5
    @7
    @2
    @3
    cF
    caov
    cS
    @2
    @3
    cF
    df-aov
    aoprssdm.1
    syl5eqelr
    @4
    cS
    cF
    afvvdm
    syl
    sylbi
    relssi
end
