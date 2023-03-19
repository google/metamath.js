include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "kmlem6.mm"
include "ralinexa.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "ralbii.mm"
include "ralnex.mm"
include "sylib.mm"

theorem kmlem7
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let vu: setvar u
  let vy: setvar y
  let wph: wff ph
  let wps: wff ps

  disjoint v x
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v y
  disjoint ph v
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint w y
  disjoint y z
  assert |- ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> -. E. z e. x A. v e. z E. w e. x ( z =/= w /\ v e. ( z i^i w ) ) )

  proof
    vz
    cv
    #
    c0
    wne
    vz
    vx
    cv
    #
    wral
    @0
    vw
    cv
    #
    wne
    #
    @0
    @2
    cin
    #
    c0
    wceq
    wi
    vw
    @1
    wral
    vz
    @1
    wral
    wa
    @3
    vv
    cv
    @4
    wcel
    #
    wn
    wi
    vw
    @1
    wral
    #
    vv
    @0
    wrex
    #
    vz
    @1
    wral
    #
    @3
    @5
    wa
    vw
    @1
    wrex
    #
    vv
    @0
    wral
    #
    vz
    @1
    wrex
    wn
    #
    @3
    vx
    vz
    vw
    vv
    @4
    kmlem6
    @8
    @10
    wn
    #
    vz
    @1
    wral
    @11
    @7
    @12
    vz
    @1
    @7
    @9
    wn
    #
    vv
    @0
    wrex
    @12
    @6
    @13
    vv
    @0
    @3
    @5
    vw
    @1
    ralinexa
    rexbii
    @9
    vv
    @0
    rexnal
    bitri
    ralbii
    @10
    vz
    @1
    ralnex
    bitri
    sylib
end
