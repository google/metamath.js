include "wcel.mm"
include "cvv.mm"
include "cun.mm"
include "elex.mm"
include "wa.mm"
include "unexb.mm"
include "biimpi.mm"
include "syl2an.mm"

theorem unexg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A u. B ) e. _V )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    cun
    cvv
    wcel
    #
    cB
    cW
    wcel
    cA
    cV
    elex
    cB
    cW
    elex
    @0
    @1
    wa
    @2
    cA
    cB
    unexb
    biimpi
    syl2an
end
