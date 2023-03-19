include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "wpss.mm"
include "nelneq2.mm"
include "eqcom.mm"
include "sylnib.mm"
include "dfpss2.mm"
include "baibr.mm"
include "syl5ib.mm"

theorem ssnelpss
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( ( C e. B /\ -. C e. A ) -> A C. B ) )

  proof
    cC
    cB
    wcel
    cC
    cA
    wcel
    wn
    wa
    #
    cA
    cB
    wceq
    #
    wn
    #
    cA
    cB
    wss
    #
    cA
    cB
    wpss
    #
    @0
    cB
    cA
    wceq
    @1
    cC
    cB
    cA
    nelneq2
    cB
    cA
    eqcom
    sylnib
    @4
    @3
    @2
    cA
    cB
    dfpss2
    baibr
    syl5ib
end
