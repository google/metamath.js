include "wcel.mm"
include "wa.mm"
include "ccoss.mm"
include "wbr.mm"
include "cec.mm"
include "cin.mm"
include "brcosscnvcoss.mm"
include "anbi2d.mm"
include "elin.mm"
include "wrel.mm"
include "wb.mm"
include "relcoss.mm"
include "relelec.mm"
include "ax-mp.mm"
include "anbi12i.mm"
include "bitri.mm"
include "syl6rbbr.mm"

theorem eleccossin
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( B e. V /\ C e. W ) -> ( B e. ( [ A ] ,~ R i^i [ C ] ,~ R ) <-> ( A ,~ R B /\ B ,~ R C ) ) )

  proof
    cB
    cV
    wcel
    cC
    cW
    wcel
    wa
    #
    cA
    cB
    cR
    ccoss
    #
    wbr
    #
    cB
    cC
    @1
    wbr
    #
    wa
    @2
    cC
    cB
    @1
    wbr
    #
    wa
    #
    cB
    cA
    @1
    cec
    #
    cC
    @1
    cec
    #
    cin
    wcel
    #
    @0
    @3
    @4
    @2
    cB
    cC
    cR
    cV
    cW
    brcosscnvcoss
    anbi2d
    @8
    cB
    @6
    wcel
    #
    cB
    @7
    wcel
    #
    wa
    @5
    cB
    @6
    @7
    elin
    @9
    @2
    @10
    @4
    @1
    wrel
    #
    @9
    @2
    wb
    cR
    relcoss
    #
    cB
    cA
    @1
    relelec
    ax-mp
    @11
    @10
    @4
    wb
    @12
    cB
    cC
    @1
    relelec
    ax-mp
    anbi12i
    bitri
    syl6rbbr
end
