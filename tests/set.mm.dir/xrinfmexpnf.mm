include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cxr.mm"
include "wa.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "simpr.mm"
include "wceq.mm"
include "velsn.mm"
include "pnfnlt.mm"
include "breq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "adantr.mm"
include "jaod.mm"
include "ex.mm"
include "ralimdv2.mm"
include "elun1.mm"
include "anim1i.mm"
include "reximi2.mm"
include "imim2i.mm"
include "ralimi.mm"
include "a1i.mm"
include "anim12d.mm"
include "reximia.mm"

theorem xrinfmexpnf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( E. x e. RR* ( A. y e. A -. y < x /\ A. y e. RR* ( x < y -> E. z e. A z < y ) ) -> E. x e. RR* ( A. y e. ( A u. { +oo } ) -. y < x /\ A. y e. RR* ( x < y -> E. z e. ( A u. { +oo } ) z < y ) ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @1
    @0
    clt
    wbr
    #
    vz
    cv
    #
    @0
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    @3
    vy
    cA
    cpnf
    csn
    #
    cun
    #
    wral
    #
    @5
    @7
    vz
    @12
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    vx
    cxr
    @1
    cxr
    wcel
    #
    @4
    @13
    @10
    @16
    @17
    @3
    @3
    vy
    cA
    @12
    @17
    @0
    cA
    wcel
    #
    @3
    wi
    #
    @0
    @12
    wcel
    #
    @3
    wi
    @20
    @18
    @0
    @11
    wcel
    #
    wo
    @17
    @19
    wa
    #
    @3
    @0
    cA
    @11
    elun
    @22
    @18
    @3
    @21
    @17
    @19
    simpr
    @17
    @21
    @3
    wi
    @19
    @21
    @0
    cpnf
    wceq
    #
    @17
    @3
    vy
    cpnf
    velsn
    @17
    @3
    @23
    cpnf
    @1
    clt
    wbr
    #
    wn
    @1
    pnfnlt
    @23
    @2
    @24
    @0
    cpnf
    @1
    clt
    breq1
    notbid
    syl5ibrcom
    syl5bi
    adantr
    jaod
    syl5bi
    ex
    ralimdv2
    @10
    @16
    wi
    @17
    @9
    @15
    vy
    cxr
    @8
    @14
    @5
    @7
    @7
    vz
    cA
    @12
    @6
    cA
    wcel
    @6
    @12
    wcel
    @7
    @6
    cA
    @11
    elun1
    anim1i
    reximi2
    imim2i
    ralimi
    a1i
    anim12d
    reximia
end
