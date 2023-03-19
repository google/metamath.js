include "cfne.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "eleq2.mm"
include "elrab.mm"
include "wrex.mm"
include "fnessex.mm"
include "3expb.mm"
include "intminss.mm"
include "sstr.mm"
include "sylan.mm"
include "expl.mm"
include "rexlimiv.mm"
include "syl.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ssint.mm"
include "sylibr.mm"

theorem fneint
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint P x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint P y
  disjoint P z
  assert |- ( A Fne B -> |^| { x e. B | P e. x } C_ |^| { x e. A | P e. x } )

  proof
    cA
    cB
    cfne
    wbr
    #
    cP
    vx
    cv
    #
    wcel
    #
    vx
    cB
    crab
    cint
    #
    vy
    cv
    #
    wss
    #
    vy
    @2
    vx
    cA
    crab
    #
    wral
    @3
    @6
    cint
    wss
    @0
    @5
    vy
    @6
    @4
    @6
    wcel
    @4
    cA
    wcel
    #
    cP
    @4
    wcel
    #
    wa
    #
    @0
    @5
    @2
    @8
    vx
    @4
    cA
    @1
    @4
    cP
    eleq2
    elrab
    @0
    @9
    @5
    @0
    @9
    wa
    cP
    vz
    cv
    #
    wcel
    #
    @10
    @4
    wss
    #
    wa
    #
    vz
    cB
    wrex
    #
    @5
    @0
    @7
    @8
    @14
    vz
    cA
    cB
    cP
    @4
    fnessex
    3expb
    @13
    @5
    vz
    cB
    @10
    cB
    wcel
    #
    @11
    @12
    @5
    @15
    @11
    wa
    @3
    @10
    wss
    @12
    @5
    @2
    @11
    vx
    @10
    cB
    @1
    @10
    cP
    eleq2
    intminss
    @3
    @10
    @4
    sstr
    sylan
    expl
    rexlimiv
    syl
    ex
    syl5bi
    ralrimiv
    vy
    @3
    @6
    ssint
    sylibr
end
