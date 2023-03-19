include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "ccnv.mm"
include "xrinfmss.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "imbi12i.mm"
include "anbi12i.mm"
include "sylibr.mm"

theorem xrinfmss2
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
  assert |- ( A C_ RR* -> E. x e. RR* ( A. y e. A -. x `' < y /\ A. y e. RR* ( y `' < x -> E. z e. A y `' < z ) ) )

  proof
    cA
    cxr
    wss
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
    #
    vx
    cxr
    wrex
    @1
    @0
    clt
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @0
    @1
    @12
    wbr
    #
    @0
    @6
    @12
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
    #
    vx
    cxr
    wrex
    vx
    vy
    vz
    cA
    xrinfmss
    @21
    @11
    vx
    cxr
    @15
    @4
    @20
    @10
    @14
    @3
    vy
    cA
    @13
    @2
    @1
    @0
    clt
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    notbii
    ralbii
    @19
    @9
    vy
    cxr
    @16
    @5
    @18
    @8
    @0
    @1
    clt
    @23
    @22
    brcnv
    @17
    @7
    vz
    cA
    @0
    @6
    clt
    @23
    vz
    vex
    brcnv
    rexbii
    imbi12i
    ralbii
    anbi12i
    rexbii
    sylibr
end
