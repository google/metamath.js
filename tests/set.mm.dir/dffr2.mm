include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "wceq.mm"
include "df-fr.mm"
include "rabeq0.mm"
include "rexbii.mm"
include "imbi2i.mm"
include "albii.mm"
include "bitr4i.mm"

theorem dffr2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x { z e. x | z R y } = (/) ) )

  proof
    cA
    cR
    wfr
    vx
    cv
    #
    cA
    wss
    @0
    c0
    wne
    wa
    #
    vz
    cv
    vy
    cv
    cR
    wbr
    #
    wn
    vz
    @0
    wral
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    @1
    @2
    vz
    @0
    crab
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    vx
    vy
    vz
    cA
    cR
    df-fr
    @8
    @5
    vx
    @7
    @4
    @1
    @6
    @3
    vy
    @0
    @2
    vz
    @0
    rabeq0
    rexbii
    imbi2i
    albii
    bitr4i
end
