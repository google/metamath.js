include "wel.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "difss.mm"
include "sslin.mm"
include "ax-mp.mm"
include "kmlem4.mm"
include "syl5sseq.mm"
include "ss0b.mm"
include "sylib.mm"

theorem kmlem5
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vv: setvar v
  let vu: setvar u
  let vy: setvar y
  let wph: wff ph
  let wps: wff ps

  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w y
  disjoint y z
  assert |- ( ( w e. x /\ z =/= w ) -> ( ( z \ U. ( x \ { z } ) ) i^i ( w \ U. ( x \ { w } ) ) ) = (/) )

  proof
    vw
    vx
    wel
    vz
    cv
    #
    vw
    cv
    #
    wne
    wa
    #
    @0
    vx
    cv
    #
    @0
    csn
    cdif
    cuni
    cdif
    #
    @1
    @3
    @1
    csn
    cdif
    cuni
    #
    cdif
    #
    cin
    #
    c0
    wss
    @7
    c0
    wceq
    @2
    @4
    @1
    cin
    #
    @7
    c0
    @6
    @1
    wss
    @7
    @8
    wss
    @1
    @5
    difss
    @6
    @1
    @4
    sslin
    ax-mp
    vx
    vz
    vw
    kmlem4
    syl5sseq
    @7
    ss0b
    sylib
end
