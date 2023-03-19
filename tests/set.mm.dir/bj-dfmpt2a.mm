include "cmpt2.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "cop.mm"
include "wex.mm"
include "copab.mm"
include "wrex.mm"
include "df-mpt2.mm"
include "dfoprab2.mm"
include "ancom.mm"
include "anbi2i.mm"
include "anass.mm"
include "an13.mm"
include "3bitr2i.mm"
include "exbii.mm"
include "df-rex.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "opabbii.mm"
include "3eqtri.mm"

theorem bj-dfmpt2a
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let vs: setvar s

  disjoint x y
  disjoint s x
  disjoint t x
  disjoint s y
  disjoint t y
  disjoint s t
  disjoint A s
  disjoint A t
  disjoint B s
  disjoint B t
  disjoint C s
  disjoint C t
  disjoint A y
  assert |- ( x e. A , y e. B |-> C ) = { <. s , t >. | E. x e. A E. y e. B ( s = <. x , y >. /\ t = C ) }

  proof
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vt
    cv
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vt
    coprab
    vs
    cv
    @0
    @2
    cop
    wceq
    #
    @6
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vs
    vt
    copab
    @7
    @5
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    vs
    vt
    copab
    vx
    vy
    vt
    cA
    cB
    cC
    df-mpt2
    @6
    vx
    vy
    vt
    vs
    dfoprab2
    @10
    @13
    vs
    vt
    @10
    @1
    @12
    wa
    #
    vx
    wex
    @13
    @9
    @14
    vx
    @9
    @3
    @1
    @11
    wa
    #
    wa
    #
    vy
    wex
    @15
    vy
    cB
    wrex
    @14
    @8
    @16
    vy
    @8
    @7
    @5
    @4
    wa
    #
    wa
    @11
    @4
    wa
    @16
    @6
    @17
    @7
    @4
    @5
    ancom
    anbi2i
    @7
    @5
    @4
    anass
    @11
    @1
    @3
    an13
    3bitr2i
    exbii
    @15
    vy
    cB
    df-rex
    @1
    @11
    vy
    cB
    r19.42v
    3bitr2i
    exbii
    @12
    vx
    cA
    df-rex
    bitr4i
    opabbii
    3eqtri
end
