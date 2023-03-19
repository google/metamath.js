include "crn.mm"
include "wss.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cxp.mm"
include "ciun.mm"
include "relcnv.mm"
include "wrel.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "vex.mm"
include "opeldm.mm"
include "df-rn.mm"
include "syl6eleqr.mm"
include "ssel2.mm"
include "sylan2.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "elimasn.mm"
include "anbi2i.mm"
include "syl6bbr.mm"
include "wceq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "opeliunxp2.mm"
include "eqrelrdv.mm"

theorem dfcnv2
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint R x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R y
  disjoint R z
  assert |- ( ran R C_ A -> `' R = U_ x e. A ( { x } X. ( `' R " { x } ) ) )

  proof
    cR
    crn
    #
    cA
    wss
    #
    vz
    vy
    cR
    ccnv
    #
    vx
    cA
    vx
    cv
    #
    csn
    #
    @2
    @4
    cima
    #
    cxp
    #
    ciun
    #
    cR
    relcnv
    @7
    wrel
    @6
    wrel
    #
    vx
    cA
    wral
    @8
    vx
    cA
    @4
    @5
    relxp
    rgenw
    vx
    cA
    @6
    reliun
    mpbir
    @1
    vz
    cv
    #
    vy
    cv
    #
    cop
    #
    @2
    wcel
    #
    @9
    cA
    wcel
    #
    @10
    @2
    @9
    csn
    #
    cima
    #
    wcel
    #
    wa
    #
    @11
    @7
    wcel
    @1
    @12
    @13
    @12
    wa
    @17
    @1
    @12
    @13
    @1
    @12
    @13
    @12
    @1
    @9
    @0
    wcel
    @13
    @12
    @9
    @2
    cdm
    @0
    @9
    @10
    @2
    vz
    vex
    #
    vy
    vex
    #
    opeldm
    cR
    df-rn
    syl6eleqr
    @0
    cA
    @9
    ssel2
    sylan2
    ex
    pm4.71rd
    @16
    @12
    @13
    @2
    @9
    @10
    @18
    @19
    elimasn
    anbi2i
    syl6bbr
    vx
    cA
    @5
    @9
    @10
    @15
    @3
    @9
    wceq
    @4
    @14
    @2
    @3
    @9
    sneq
    imaeq2d
    opeliunxp2
    syl6bbr
    eqrelrdv
end
