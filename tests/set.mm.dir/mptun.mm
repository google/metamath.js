include "cun.mm"
include "cmpt.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "uneq12i.mm"
include "wo.mm"
include "elun.mm"
include "anbi1i.mm"
include "andir.mm"
include "bitri.mm"
include "opabbii.mm"
include "unopab.mm"
include "eqtr4i.mm"

theorem mptun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( x e. ( A u. B ) |-> C ) = ( ( x e. A |-> C ) u. ( x e. B |-> C ) )

  proof
    vx
    cA
    cB
    cun
    #
    cC
    cmpt
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    cC
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    vx
    cA
    cC
    cmpt
    #
    vx
    cB
    cC
    cmpt
    #
    cun
    #
    vx
    vy
    @0
    cC
    df-mpt
    @8
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    #
    @1
    cB
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    #
    cun
    #
    @5
    @6
    @11
    @7
    @14
    vx
    vy
    cA
    cC
    df-mpt
    vx
    vy
    cB
    cC
    df-mpt
    uneq12i
    @5
    @10
    @13
    wo
    #
    vx
    vy
    copab
    @15
    @4
    @16
    vx
    vy
    @4
    @9
    @12
    wo
    #
    @3
    wa
    @16
    @2
    @17
    @3
    @1
    cA
    cB
    elun
    anbi1i
    @9
    @12
    @3
    andir
    bitri
    opabbii
    @10
    @13
    vx
    vy
    unopab
    eqtr4i
    eqtr4i
    eqtr4i
end
