include "wer.mm"
include "wbr.mm"
include "wa.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "ertr3d.mm"
include "ertrd.mm"
include "impbida.mm"

theorem erbr3b
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X


  assert |- ( ( R Er X /\ A R B ) -> ( A R C <-> B R C ) )

  proof
    cX
    cR
    wer
    #
    cA
    cB
    cR
    wbr
    #
    wa
    #
    cA
    cC
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    @2
    @3
    wa
    cB
    cA
    cC
    cR
    cX
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    @2
    @3
    simpr
    ertr3d
    @2
    @4
    wa
    cA
    cB
    cC
    cR
    cX
    @0
    @1
    @4
    simpll
    @0
    @1
    @4
    simplr
    @2
    @4
    simpr
    ertrd
    impbida
end
