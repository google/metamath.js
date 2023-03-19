include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wrel.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "elrel.mm"
include "mpan.mm"
include "excom.mm"
include "sylibr.mm"
include "pm4.71ri.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "19.41.mm"
include "19.41v.mm"
include "eleq1.mm"
include "opeliun2xp.mm"
include "ancom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "bitr3i.mm"
include "3bitr2i.mm"

theorem eliunxp2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint k x
  assert |- ( C e. U_ y e. B ( A X. { y } ) <-> E. x E. y ( C = <. x , y >. /\ ( x e. A /\ y e. B ) ) )

  proof
    cC
    vy
    cB
    cA
    vy
    cv
    #
    csn
    #
    cxp
    #
    ciun
    #
    wcel
    #
    cC
    vx
    cv
    #
    @0
    cop
    #
    wceq
    #
    @5
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    vy
    wex
    #
    @11
    vy
    wex
    vx
    wex
    @4
    @7
    vx
    wex
    #
    vy
    wex
    #
    @4
    wa
    @14
    @4
    wa
    #
    vy
    wex
    @13
    @4
    @15
    @4
    @7
    vy
    wex
    vx
    wex
    #
    @15
    @3
    wrel
    #
    @4
    @17
    @18
    @2
    wrel
    #
    vy
    cB
    wral
    @19
    vy
    cB
    cA
    @1
    relxp
    rgenw
    vy
    cB
    @2
    reliun
    mpbir
    vx
    vy
    cC
    @3
    elrel
    mpan
    @7
    vy
    vx
    excom
    sylibr
    pm4.71ri
    @14
    @4
    vy
    vy
    cC
    @3
    vy
    cB
    @2
    nfiu1
    nfel2
    19.41
    @16
    @12
    vy
    @16
    @7
    @4
    wa
    #
    vx
    wex
    @12
    @7
    @4
    vx
    19.41v
    @20
    @11
    vx
    @7
    @4
    @10
    @7
    @4
    @6
    @3
    wcel
    #
    @10
    cC
    @6
    @3
    eleq1
    @21
    @9
    @8
    wa
    @10
    vy
    cA
    cB
    @5
    opeliun2xp
    @9
    @8
    ancom
    bitri
    syl6bb
    pm5.32i
    exbii
    bitr3i
    exbii
    3bitr2i
    @11
    vy
    vx
    excom
    bitri
end
