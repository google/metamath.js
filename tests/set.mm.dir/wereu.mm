include "wwe.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "wfr.mm"
include "wefr.mm"
include "wi.mm"
include "fri.mm"
include "exp32.mm"
include "expcom.mm"
include "3imp2.mm"
include "sylan.mm"
include "wor.mm"
include "weso.mm"
include "soss.mm"
include "mpan9.mm"
include "somo.mm"
include "syl.mm"
include "3ad2antr2.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem wereu
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint R w
  disjoint R z
  assert |- ( ( R We A /\ ( B e. V /\ B C_ A /\ B =/= (/) ) ) -> E! x e. B A. y e. B -. y R x )

  proof
    cA
    cR
    wwe
    #
    cB
    cV
    wcel
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    w3a
    #
    wa
    vy
    cv
    vx
    cv
    cR
    wbr
    wn
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @5
    vx
    cB
    wrmo
    #
    @5
    vx
    cB
    wreu
    @0
    cA
    cR
    wfr
    #
    @4
    @6
    cA
    cR
    wefr
    @8
    @1
    @2
    @3
    @6
    @1
    @8
    @2
    @3
    @6
    wi
    wi
    @1
    @8
    wa
    @2
    @3
    @6
    vx
    vy
    cA
    cB
    cV
    cR
    fri
    exp32
    expcom
    3imp2
    sylan
    @0
    @1
    @2
    @7
    @3
    @0
    @2
    wa
    cB
    cR
    wor
    #
    @7
    @0
    cA
    cR
    wor
    @2
    @9
    cA
    cR
    weso
    cB
    cA
    cR
    soss
    mpan9
    vx
    vy
    cB
    cR
    somo
    syl
    3ad2antr2
    @5
    vx
    cB
    reu5
    sylanbrc
end
