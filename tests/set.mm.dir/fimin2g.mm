include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "wfr.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "3simpc.mm"
include "wpo.mm"
include "sopo.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "frfi.mm"
include "syl2anc.mm"
include "wss.mm"
include "ssid.mm"
include "fri.mm"
include "mpanr1.mm"
include "an32s.mm"

theorem fimin2g
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
  assert |- ( ( R Or A /\ A e. Fin /\ A =/= (/) ) -> E. x e. A A. y e. A -. y R x )

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
    #
    @1
    @2
    wa
    cA
    cR
    wfr
    #
    vy
    cv
    vx
    cv
    cR
    wbr
    wn
    vy
    cA
    wral
    vx
    cA
    wrex
    #
    @0
    @1
    @2
    3simpc
    @3
    cA
    cR
    wpo
    #
    @1
    @4
    @0
    @1
    @6
    @2
    cA
    cR
    sopo
    3ad2ant1
    @0
    @1
    @2
    simp2
    cA
    cR
    frfi
    syl2anc
    @1
    @4
    @2
    @5
    @1
    @4
    wa
    cA
    cA
    wss
    @2
    @5
    cA
    ssid
    vx
    vy
    cA
    cA
    cfn
    cR
    fri
    mpanr1
    an32s
    syl2anc
end
