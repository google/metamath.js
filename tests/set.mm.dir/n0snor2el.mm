include "weq.mm"
include "wral.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "wo.mm"
include "wi.mm"
include "issn.mm"
include "olcd.mm"
include "a1d.mm"
include "wn.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "ralbii.mm"
include "ralnex.mm"
include "wa.mm"
include "neeq1.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "reximdva0.mm"
include "orcd.mm"
include "ex.mm"
include "sylbir.mm"
include "pm2.61i.mm"

theorem n0snor2el
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( A =/= (/) -> ( E. x e. A E. y e. A x =/= y \/ E. z A = { z } ) )

  proof
    vw
    vy
    weq
    #
    vy
    cA
    wral
    #
    vw
    cA
    wrex
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    cA
    vz
    cv
    csn
    wceq
    vz
    wex
    #
    wo
    #
    wi
    #
    @2
    @10
    @3
    @2
    @9
    @8
    vw
    vy
    vz
    cA
    issn
    olcd
    a1d
    @2
    wn
    #
    vw
    cv
    #
    @5
    wne
    #
    vy
    cA
    wrex
    #
    vw
    cA
    wral
    #
    @11
    @16
    @1
    wn
    #
    vw
    cA
    wral
    @12
    @15
    @17
    vw
    cA
    @15
    @0
    wn
    #
    vy
    cA
    wrex
    @17
    @14
    @18
    vy
    cA
    @13
    @5
    df-ne
    rexbii
    @0
    vy
    cA
    rexnal
    bitri
    ralbii
    @1
    vw
    cA
    ralnex
    bitri
    @16
    @3
    @10
    @16
    @3
    wa
    @8
    @9
    @16
    @7
    vx
    cA
    @15
    @7
    vw
    @4
    cA
    vw
    vx
    weq
    @14
    @6
    vy
    cA
    @13
    @4
    @5
    neeq1
    rexbidv
    rspccva
    reximdva0
    orcd
    ex
    sylbir
    pm2.61i
end
