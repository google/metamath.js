include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cdom.mm"
include "wbr.mm"
include "ccda.mm"
include "co.mm"
include "cvv.mm"
include "wss.mm"
include "unexg.mm"
include "ssun1.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "uncdadom.mm"
include "domtr.mm"
include "syl2anc.mm"

theorem cdadom3
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> A ~<_ ( A +c B ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cA
    cB
    cun
    #
    cdom
    wbr
    #
    @1
    cA
    cB
    ccda
    co
    #
    cdom
    wbr
    cA
    @3
    cdom
    wbr
    @0
    @1
    cvv
    wcel
    cA
    @1
    wss
    @2
    cA
    cB
    cV
    cW
    unexg
    cA
    cB
    ssun1
    cA
    @1
    cvv
    ssdomg
    mpisyl
    cA
    cB
    cV
    cW
    uncdadom
    cA
    @1
    @3
    domtr
    syl2anc
end
