include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cdm.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "r1ord3g.mm"
include "syl2anbr.mm"

theorem r1ord3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B -> ( R1 ` A ) C_ ( R1 ` B ) ) )

  proof
    cA
    con0
    wcel
    cA
    cr1
    cdm
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    wss
    cA
    cr1
    cfv
    cB
    cr1
    cfv
    wss
    wi
    cB
    con0
    wcel
    @0
    con0
    cA
    cr1
    con0
    wfn
    @0
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    #
    eleq2i
    @0
    con0
    cB
    @1
    eleq2i
    cA
    cB
    r1ord3g
    syl2anbr
end
