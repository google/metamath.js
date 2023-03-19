include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cab.mm"
include "tgval2.mm"
include "eleq2d.mm"
include "cvv.mm"
include "elex.mm"
include "adantl.mm"
include "uniexg.mm"
include "ssexg.mm"
include "sylan2.mm"
include "ancoms.mm"
include "adantrr.mm"
include "wceq.mm"
include "sseq1.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elabg.mm"
include "pm5.21nd.mm"
include "bitrd.mm"

theorem eltg2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint V y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( B e. V -> ( A e. ( topGen ` B ) <-> ( A C_ U. B /\ A. x e. A E. y e. B ( x e. y /\ y C_ A ) ) ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    ctg
    cfv
    #
    wcel
    cA
    vz
    cv
    #
    cB
    cuni
    #
    wss
    #
    vx
    cv
    vy
    cv
    #
    wcel
    #
    @5
    @2
    wss
    #
    wa
    #
    vy
    cB
    wrex
    #
    vx
    @2
    wral
    #
    wa
    #
    vz
    cab
    #
    wcel
    #
    cA
    @3
    wss
    #
    @6
    @5
    cA
    wss
    #
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    @0
    @1
    @12
    cA
    vz
    vx
    vy
    cB
    cV
    tgval2
    eleq2d
    @0
    @13
    @19
    cA
    cvv
    wcel
    #
    @13
    @20
    @0
    cA
    @12
    elex
    adantl
    @0
    @14
    @20
    @18
    @14
    @0
    @20
    @0
    @14
    @3
    cvv
    wcel
    @20
    cB
    cV
    uniexg
    cA
    @3
    cvv
    ssexg
    sylan2
    ancoms
    adantrr
    @11
    @19
    vz
    cA
    cvv
    @2
    cA
    wceq
    #
    @4
    @14
    @10
    @18
    @2
    cA
    @3
    sseq1
    @9
    @17
    vx
    @2
    cA
    @21
    @8
    @16
    vy
    cB
    @21
    @7
    @15
    @6
    @2
    cA
    @5
    sseq2
    anbi2d
    rexbidv
    raleqbi1dv
    anbi12d
    elabg
    pm5.21nd
    bitrd
end
