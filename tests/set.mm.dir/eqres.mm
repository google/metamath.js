include "wbr.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "breqi.mm"
include "brresALTV.mm"
include "syl5bb.mm"

theorem eqres
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  assume eqres.1: |- R = ( S |` C )


  assert |- ( B e. V -> ( A R B <-> ( A e. C /\ A S B ) ) )

  proof
    cA
    cB
    cR
    wbr
    cA
    cB
    cS
    cC
    cres
    #
    wbr
    cB
    cV
    wcel
    cA
    cC
    wcel
    cA
    cB
    cS
    wbr
    wa
    cA
    cB
    cR
    @0
    eqres.1
    breqi
    cC
    cA
    cB
    cS
    cV
    brresALTV
    syl5bb
end
