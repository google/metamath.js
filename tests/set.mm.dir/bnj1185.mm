include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "rexbii.mm"
include "sylib.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "eleq1.mm"
include "breq2.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "df-rex.mm"
include "3bitr4ri.mm"
include "sylibr.mm"

theorem bnj1185
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cR: class R
  assume bnj1185.1: |- ( ph -> E. z e. B A. w e. B -. w R z )

  disjoint B w
  disjoint B y
  disjoint B z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint R x
  assert |- ( ph -> E. x e. B A. y e. B -. y R x )

  proof
    wph
    vy
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vz
    cB
    wrex
    #
    @0
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    wph
    vw
    cv
    #
    @1
    cR
    wbr
    #
    wn
    #
    vw
    cB
    wral
    #
    vz
    cB
    wrex
    @5
    bnj1185.1
    @14
    @4
    vz
    cB
    @13
    @3
    vw
    vy
    cB
    vw
    vy
    weq
    @12
    @2
    @11
    @0
    @1
    cR
    breq1
    notbid
    cbvralv
    rexbii
    sylib
    @1
    cB
    wcel
    #
    @4
    wa
    #
    vz
    wex
    @6
    cB
    wcel
    #
    @9
    wa
    #
    vx
    wex
    @5
    @10
    @16
    @18
    vz
    vx
    vz
    vx
    weq
    #
    @15
    @17
    @4
    @9
    @1
    @6
    cB
    eleq1
    @19
    @3
    @8
    vy
    cB
    @19
    @2
    @7
    @1
    @6
    @0
    cR
    breq2
    notbid
    ralbidv
    anbi12d
    cbvexv
    @4
    vz
    cB
    df-rex
    @9
    vx
    cB
    df-rex
    3bitr4ri
    sylibr
end
