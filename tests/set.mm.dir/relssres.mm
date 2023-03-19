include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "wceq.mm"
include "simpl.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "vex.mm"
include "opeldm.mm"
include "ssel.mm"
include "syl5.mm"
include "ancld.mm"
include "opelres.mm"
include "syl6ibr.mm"
include "adantl.mm"
include "relssdv.mm"
include "resss.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"

theorem relssres
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( Rel A /\ dom A C_ B ) -> ( A |` B ) = A )

  proof
    cA
    wrel
    #
    cA
    cdm
    #
    cB
    wss
    #
    wa
    #
    cA
    cB
    cres
    #
    cA
    wss
    #
    cA
    @4
    wss
    #
    wa
    @4
    cA
    wceq
    @3
    @6
    @5
    @3
    vx
    vy
    cA
    @4
    @0
    @2
    simpl
    @2
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @9
    @4
    wcel
    #
    wi
    @0
    @2
    @10
    @10
    @7
    cB
    wcel
    #
    wa
    @11
    @2
    @10
    @12
    @10
    @7
    @1
    wcel
    @2
    @12
    @7
    @8
    cA
    vx
    vex
    vy
    vex
    #
    opeldm
    @1
    cB
    @7
    ssel
    syl5
    ancld
    @7
    @8
    cA
    cB
    @13
    opelres
    syl6ibr
    adantl
    relssdv
    cA
    cB
    resss
    jctil
    @4
    cA
    eqss
    sylibr
end
