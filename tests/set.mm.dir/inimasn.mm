include "wcel.mm"
include "cin.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wa.mm"
include "elin.mm"
include "cop.mm"
include "wb.mm"
include "a1i.mm"
include "cvv.mm"
include "vex.mm"
include "elimasng.mm"
include "mpan2.mm"
include "anbi12d.mm"
include "3bitr4rd.mm"
include "syl5rbb.mm"
include "eqrdv.mm"

theorem inimasn
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x


  assert |- ( C e. V -> ( ( A i^i B ) " { C } ) = ( ( A " { C } ) i^i ( B " { C } ) ) )

  proof
    cC
    cV
    wcel
    #
    vx
    cA
    cB
    cin
    #
    cC
    csn
    #
    cima
    #
    cA
    @2
    cima
    #
    cB
    @2
    cima
    #
    cin
    #
    vx
    cv
    #
    @6
    wcel
    @7
    @4
    wcel
    #
    @7
    @5
    wcel
    #
    wa
    #
    @0
    @7
    @3
    wcel
    #
    @7
    @4
    @5
    elin
    @0
    cC
    @7
    cop
    #
    @1
    wcel
    #
    @12
    cA
    wcel
    #
    @12
    cB
    wcel
    #
    wa
    #
    @11
    @10
    @13
    @16
    wb
    @0
    @12
    cA
    cB
    elin
    a1i
    @0
    @7
    cvv
    wcel
    #
    @11
    @13
    wb
    vx
    vex
    #
    @1
    cC
    @7
    cV
    cvv
    elimasng
    mpan2
    @0
    @8
    @14
    @9
    @15
    @0
    @17
    @8
    @14
    wb
    @18
    cA
    cC
    @7
    cV
    cvv
    elimasng
    mpan2
    @0
    @17
    @9
    @15
    wb
    @18
    cB
    cC
    @7
    cV
    cvv
    elimasng
    mpan2
    anbi12d
    3bitr4rd
    syl5rbb
    eqrdv
end
