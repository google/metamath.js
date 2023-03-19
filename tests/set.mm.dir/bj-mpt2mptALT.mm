include "cv.mm"
include "cxp.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cop.mm"
include "wrex.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "elxp2.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "3bitr2i.mm"
include "opabbii.mm"
include "df-mpt.mm"
include "bj-dfmpt2a.mm"
include "3eqtr4i.mm"

theorem bj-mpt2mptALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vt: setvar t
  assume bj-mpt2mptALT.1: |- ( z = <. x , y >. -> C = D )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint B t
  disjoint C t
  disjoint D t
  assert |- ( z e. ( A X. B ) |-> C ) = ( x e. A , y e. B |-> D )

  proof
    vz
    cv
    #
    cA
    cB
    cxp
    #
    wcel
    #
    vt
    cv
    #
    cC
    wceq
    #
    wa
    #
    vz
    vt
    copab
    @0
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    @3
    cD
    wceq
    #
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
    vz
    vt
    copab
    vz
    @1
    cC
    cmpt
    vx
    vy
    cA
    cB
    cD
    cmpt2
    @5
    @10
    vz
    vt
    @5
    @6
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    @4
    wa
    @11
    @4
    wa
    #
    vx
    cA
    wrex
    @10
    @2
    @12
    @4
    vx
    vy
    @0
    cA
    cB
    elxp2
    anbi1i
    @11
    @4
    vx
    cA
    r19.41v
    @13
    @9
    vx
    cA
    @13
    @6
    @4
    wa
    #
    vy
    cB
    wrex
    @9
    @6
    @4
    vy
    cB
    r19.41v
    @14
    @8
    vy
    cB
    @6
    @4
    @7
    @6
    cC
    cD
    @3
    bj-mpt2mptALT.1
    eqeq2d
    pm5.32i
    rexbii
    bitr3i
    rexbii
    3bitr2i
    opabbii
    vz
    vt
    @1
    cC
    df-mpt
    vx
    vy
    vt
    cA
    cB
    cD
    vz
    bj-dfmpt2a
    3eqtr4i
end
