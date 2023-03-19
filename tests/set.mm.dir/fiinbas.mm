include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "ctb.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "ssid.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "ralrimiva.mm"
include "a1i.mm"
include "ralimdv.mm"
include "isbasis2g.mm"
include "sylibrd.mm"
include "imp.mm"

theorem fiinbas
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint C w
  disjoint C z
  assert |- ( ( B e. C /\ A. x e. B A. y e. B ( x i^i y ) e. B ) -> B e. TopBases )

  proof
    cB
    cC
    wcel
    #
    vx
    cv
    vy
    cv
    cin
    #
    cB
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    cB
    ctb
    wcel
    #
    @0
    @4
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @7
    @1
    wss
    #
    wa
    #
    vw
    cB
    wrex
    #
    vz
    @1
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @5
    @0
    @3
    @13
    vx
    cB
    @0
    @2
    @12
    vy
    cB
    @2
    @12
    wi
    @0
    @2
    @11
    vz
    @1
    @2
    @6
    @1
    wcel
    #
    @1
    @1
    wss
    #
    @11
    @1
    ssid
    @10
    @14
    @15
    wa
    vw
    @1
    cB
    @7
    @1
    wceq
    @8
    @14
    @9
    @15
    @7
    @1
    @6
    eleq2
    @7
    @1
    @1
    sseq1
    anbi12d
    rspcev
    mpanr2
    ralrimiva
    a1i
    ralimdv
    ralimdv
    vx
    vy
    vz
    vw
    cB
    cC
    isbasis2g
    sylibrd
    imp
end
