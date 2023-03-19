include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wpo.mm"
include "breq.mm"
include "notbid.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "df-po.mm"
include "3bitr4g.mm"

theorem poeq1
  let cA: class A
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R = S -> ( R Po A <-> S Po A ) )

  proof
    cR
    cS
    wceq
    #
    vx
    cv
    #
    @1
    cR
    wbr
    #
    wn
    #
    @1
    vy
    cv
    #
    cR
    wbr
    #
    @4
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @1
    @6
    cR
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @1
    @1
    cS
    wbr
    #
    wn
    #
    @1
    @4
    cS
    wbr
    #
    @4
    @6
    cS
    wbr
    #
    wa
    #
    @1
    @6
    cS
    wbr
    #
    wi
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    cR
    wpo
    cA
    cS
    wpo
    @0
    @12
    @21
    vx
    vy
    cA
    cA
    @0
    @11
    @20
    vz
    cA
    @0
    @3
    @14
    @10
    @19
    @0
    @2
    @13
    @1
    @1
    cR
    cS
    breq
    notbid
    @0
    @8
    @17
    @9
    @18
    @0
    @5
    @15
    @7
    @16
    @1
    @4
    cR
    cS
    breq
    @4
    @6
    cR
    cS
    breq
    anbi12d
    @1
    @6
    cR
    cS
    breq
    imbi12d
    anbi12d
    ralbidv
    2ralbidv
    vx
    vy
    vz
    cA
    cR
    df-po
    vx
    vy
    vz
    cA
    cS
    df-po
    3bitr4g
end
