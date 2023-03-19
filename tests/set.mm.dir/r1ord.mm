include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cdm.mm"
include "cfv.mm"
include "wi.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "r1ordg.mm"
include "sylbir.mm"

theorem r1ord
  let cA: class A
  let cB: class B


  assert |- ( B e. On -> ( A e. B -> ( R1 ` A ) e. ( R1 ` B ) ) )

  proof
    cB
    con0
    wcel
    cB
    cr1
    cdm
    #
    wcel
    cA
    cB
    wcel
    cA
    cr1
    cfv
    cB
    cr1
    cfv
    wcel
    wi
    @0
    con0
    cB
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
    eleq2i
    cA
    cB
    r1ordg
    sylbir
end
