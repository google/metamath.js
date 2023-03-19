include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "rgen.mm"
include "sseq1.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mp2ani.mm"
include "fvex.mm"
include "isseti.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "exbii.mm"
include "excom.mm"
include "bitr3i.mm"
include "sylib.mm"

theorem cflem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cV: class V
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  disjoint A v
  assert |- ( A e. V -> E. x E. y ( x = ( card ` y ) /\ ( y C_ A /\ A. z e. A E. w e. y z C_ w ) ) )

  proof
    cA
    cV
    wcel
    #
    vy
    cv
    #
    cA
    wss
    #
    vz
    cv
    #
    vw
    cv
    #
    wss
    #
    vw
    @1
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    vy
    wex
    #
    vx
    cv
    @1
    ccrd
    cfv
    #
    wceq
    #
    @8
    wa
    #
    vy
    wex
    vx
    wex
    #
    @0
    cA
    cA
    wss
    #
    @5
    vw
    cA
    wrex
    #
    vz
    cA
    wral
    #
    @9
    cA
    ssid
    @15
    vz
    cA
    @3
    cA
    wcel
    @3
    @3
    wss
    #
    @15
    @3
    ssid
    @5
    @17
    vw
    @3
    cA
    @4
    @3
    @3
    sseq2
    rspcev
    mpan2
    rgen
    @8
    @14
    @16
    wa
    vy
    cA
    cV
    @1
    cA
    wceq
    #
    @2
    @14
    @7
    @16
    @1
    cA
    cA
    sseq1
    @18
    @6
    @15
    vz
    cA
    @5
    vw
    @1
    cA
    rexeq
    ralbidv
    anbi12d
    spcegv
    mp2ani
    @9
    @12
    vx
    wex
    #
    vy
    wex
    @13
    @19
    @8
    vy
    @19
    @11
    vx
    wex
    @8
    vx
    @10
    @1
    ccrd
    fvex
    isseti
    @11
    @8
    vx
    19.41v
    mpbiran
    exbii
    @12
    vy
    vx
    excom
    bitr3i
    sylib
end
