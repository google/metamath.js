include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "wrel.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "elrel.mm"
include "mpan.mm"
include "pm4.71ri.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "19.41.mm"
include "19.41v.mm"
include "eleq1.mm"
include "opeliunxp.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "bitr3i.mm"
include "3bitr2i.mm"

theorem eliunxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E

  disjoint A y
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint E x
  assert |- ( C e. U_ x e. A ( { x } X. B ) <-> E. x E. y ( C = <. x , y >. /\ ( x e. A /\ y e. B ) ) )

  proof
    cC
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    wcel
    #
    cC
    @0
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    #
    vx
    wex
    #
    @4
    wa
    @8
    @4
    wa
    #
    vx
    wex
    @7
    @0
    cA
    wcel
    @5
    cB
    wcel
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    @4
    @9
    @3
    wrel
    #
    @4
    @9
    @14
    @2
    wrel
    #
    vx
    cA
    wral
    @15
    vx
    cA
    @1
    cB
    relxp
    rgenw
    vx
    cA
    @2
    reliun
    mpbir
    vx
    vy
    cC
    @3
    elrel
    mpan
    pm4.71ri
    @8
    @4
    vx
    vx
    cC
    @3
    vx
    cA
    @2
    nfiu1
    nfel2
    19.41
    @10
    @13
    vx
    @10
    @7
    @4
    wa
    #
    vy
    wex
    @13
    @7
    @4
    vy
    19.41v
    @16
    @12
    vy
    @7
    @4
    @11
    @7
    @4
    @6
    @3
    wcel
    @11
    cC
    @6
    @3
    eleq1
    vx
    cA
    cB
    @5
    opeliunxp
    syl6bb
    pm5.32i
    exbii
    bitr3i
    exbii
    3bitr2i
end
