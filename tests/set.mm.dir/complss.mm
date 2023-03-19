include "wss.mm"
include "cvv.mm"
include "cdif.mm"
include "sscon.mm"
include "ddif.mm"
include "3sstr3g.mm"
include "impbii.mm"

theorem complss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( _V \ B ) C_ ( _V \ A ) )

  proof
    cA
    cB
    wss
    cvv
    cB
    cdif
    #
    cvv
    cA
    cdif
    #
    wss
    #
    cA
    cB
    cvv
    sscon
    @2
    cvv
    @1
    cdif
    cvv
    @0
    cdif
    cA
    cB
    @0
    @1
    cvv
    sscon
    cA
    ddif
    cB
    ddif
    3sstr3g
    impbii
end
