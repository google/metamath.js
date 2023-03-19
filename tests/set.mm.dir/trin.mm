include "wtr.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "elin.mm"
include "trss.mm"
include "im2anan9.mm"
include "syl5bi.mm"
include "ssin.mm"
include "syl6ib.mm"
include "ralrimiv.mm"
include "dftr3.mm"
include "sylibr.mm"

theorem trin
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( Tr A /\ Tr B ) -> Tr ( A i^i B ) )

  proof
    cA
    wtr
    #
    cB
    wtr
    #
    wa
    #
    vx
    cv
    #
    cA
    cB
    cin
    #
    wss
    #
    vx
    @4
    wral
    @4
    wtr
    @2
    @5
    vx
    @4
    @2
    @3
    @4
    wcel
    #
    @3
    cA
    wss
    #
    @3
    cB
    wss
    #
    wa
    #
    @5
    @6
    @3
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    @2
    @9
    @3
    cA
    cB
    elin
    @0
    @10
    @7
    @1
    @11
    @8
    cA
    @3
    trss
    cB
    @3
    trss
    im2anan9
    syl5bi
    @3
    cA
    cB
    ssin
    syl6ib
    ralrimiv
    vx
    @4
    dftr3
    sylibr
end
