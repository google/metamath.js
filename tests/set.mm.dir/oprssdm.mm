include "cxp.mm"
include "cdm.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "opelxp.mm"
include "cfv.mm"
include "co.mm"
include "df-ov.mm"
include "syl5eqelr.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "syl.mm"
include "sylbi.mm"
include "relssi.mm"

theorem oprssdm
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  assume oprssdm.1: |- -. (/) e. S
  assume oprssdm.2: |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S )

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
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
    cfv
    #
    cS
    wcel
    #
    @6
    @5
    @7
    @2
    @3
    cF
    co
    cS
    @2
    @3
    cF
    df-ov
    oprssdm.2
    syl5eqelr
    @6
    @8
    @6
    wn
    #
    @8
    c0
    cS
    wcel
    oprssdm.1
    @9
    @7
    c0
    cS
    @4
    cF
    ndmfv
    eleq1d
    mtbiri
    con4i
    syl
    sylbi
    relssi
end
