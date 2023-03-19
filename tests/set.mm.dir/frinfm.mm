include "wfr.mm"
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
include "ccnv.mm"
include "wi.mm"
include "fri.mm"
include "ancom1s.mm"
include "exp43.mm"
include "3imp2.mm"
include "ssel2.mm"
include "adantrr.mm"
include "vex.mm"
include "brcnv.mm"
include "biimpi.mm"
include "con3i.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimivw.mm"
include "ad2antrl.mm"
include "jca32.mm"
include "reximdv2.mm"
include "adantl.mm"
include "3ad2antr2.mm"
include "mpd.mm"

theorem frinfm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( ( R Fr A /\ ( B e. C /\ B C_ A /\ B =/= (/) ) ) -> E. x e. A ( A. y e. B -. x `' R y /\ A. y e. A ( y `' R x -> E. z e. B y `' R z ) ) )

  proof
    cA
    cR
    wfr
    #
    cB
    cC
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
    wa
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @5
    @4
    cR
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @4
    @5
    @10
    wbr
    #
    @4
    vz
    cv
    #
    @10
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    #
    @0
    @1
    @2
    @3
    @9
    @0
    @1
    @2
    @3
    @9
    @1
    @0
    @2
    @3
    wa
    @9
    vx
    vy
    cA
    cB
    cC
    cR
    fri
    ancom1s
    exp43
    3imp2
    @0
    @1
    @2
    @9
    @21
    wi
    #
    @3
    @2
    @22
    @0
    @2
    @8
    @20
    vx
    cB
    cA
    @2
    @5
    cB
    wcel
    #
    @8
    wa
    #
    @5
    cA
    wcel
    #
    @20
    wa
    @2
    @24
    wa
    @25
    @13
    @19
    @2
    @23
    @25
    @8
    cB
    cA
    @5
    ssel2
    adantrr
    @8
    @13
    @2
    @23
    @7
    @12
    vy
    cB
    @11
    @6
    @11
    @6
    @5
    @4
    cR
    vx
    vex
    vy
    vex
    brcnv
    biimpi
    con3i
    ralimi
    ad2antll
    @23
    @19
    @2
    @8
    @23
    @18
    vy
    cA
    @23
    @14
    @17
    @16
    @14
    vz
    @5
    cB
    @15
    @5
    @4
    @10
    breq2
    rspcev
    ex
    ralrimivw
    ad2antrl
    jca32
    ex
    reximdv2
    adantl
    3ad2antr2
    mpd
end
