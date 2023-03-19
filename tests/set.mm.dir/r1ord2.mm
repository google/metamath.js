include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "wss.mm"
include "r1ord.mm"
include "wtr.mm"
include "wi.mm"
include "r1tr.mm"
include "trss.mm"
include "ax-mp.mm"
include "syl6.mm"

theorem r1ord2
  let cA: class A
  let cB: class B


  assert |- ( B e. On -> ( A e. B -> ( R1 ` A ) C_ ( R1 ` B ) ) )

  proof
    cB
    con0
    wcel
    cA
    cB
    wcel
    cA
    cr1
    cfv
    #
    cB
    cr1
    cfv
    #
    wcel
    #
    @0
    @1
    wss
    #
    cA
    cB
    r1ord
    @1
    wtr
    @2
    @3
    wi
    cB
    r1tr
    @1
    @0
    trss
    ax-mp
    syl6
end
