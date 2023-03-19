include "wss.mm"
include "cv.mm"
include "wnel.mm"
include "wrex.mm"
include "wpss.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "df-nel.mm"
include "ssnelpss.mm"
include "expdimp.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "imp.mm"

theorem ssexnelpss
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ B /\ E. x e. B x e/ A ) -> A C. B )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wnel
    #
    vx
    cB
    wrex
    cA
    cB
    wpss
    #
    @0
    @2
    @3
    vx
    cB
    @2
    @1
    cA
    wcel
    wn
    #
    @0
    @1
    cB
    wcel
    #
    wa
    @3
    @1
    cA
    df-nel
    @0
    @5
    @4
    @3
    cA
    cB
    @1
    ssnelpss
    expdimp
    syl5bi
    rexlimdva
    imp
end
