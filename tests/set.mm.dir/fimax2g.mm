include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "ccnv.mm"
include "wfr.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wpo.mm"
include "sopo.mm"
include "cnvpo.mm"
include "sylib.mm"
include "frfi.mm"
include "sylan.mm"
include "3adant3.mm"
include "wi.mm"
include "wa.mm"
include "wss.mm"
include "ssid.mm"
include "fri.mm"
include "mpanr1.mm"
include "an32s.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "ex.mm"
include "3adant1.mm"
include "mpd.mm"

theorem fimax2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( R Or A /\ A e. Fin /\ A =/= (/) ) -> E. x e. A A. y e. A -. x R y )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    cA
    cR
    ccnv
    #
    wfr
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @0
    @1
    @4
    @2
    @0
    cA
    @3
    wpo
    #
    @1
    @4
    @0
    cA
    cR
    wpo
    @11
    cA
    cR
    sopo
    cA
    cR
    cnvpo
    sylib
    cA
    @3
    frfi
    sylan
    3adant3
    @1
    @2
    @4
    @10
    wi
    @0
    @1
    @2
    wa
    #
    @4
    @10
    @12
    @4
    wa
    @6
    @5
    @3
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @10
    @1
    @4
    @2
    @16
    @1
    @4
    wa
    cA
    cA
    wss
    @2
    @16
    cA
    ssid
    vx
    vy
    cA
    cA
    cfn
    @3
    fri
    mpanr1
    an32s
    @15
    @9
    vx
    cA
    @14
    @8
    vy
    cA
    @13
    @7
    @6
    @5
    cR
    vy
    vex
    vx
    vex
    brcnv
    notbii
    ralbii
    rexbii
    sylib
    ex
    3adant1
    mpd
end
