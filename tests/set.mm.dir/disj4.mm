include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "wpss.mm"
include "wn.mm"
include "disj3.mm"
include "eqcom.mm"
include "wss.mm"
include "difss.mm"
include "dfpss2.mm"
include "mpbiran.mm"
include "con2bii.mm"
include "3bitri.mm"

theorem disj4
  let cA: class A
  let cB: class B


  assert |- ( ( A i^i B ) = (/) <-> -. ( A \ B ) C. A )

  proof
    cA
    cB
    cin
    c0
    wceq
    cA
    cA
    cB
    cdif
    #
    wceq
    @0
    cA
    wceq
    #
    @0
    cA
    wpss
    #
    wn
    cA
    cB
    disj3
    cA
    @0
    eqcom
    @2
    @1
    @2
    @0
    cA
    wss
    @1
    wn
    cA
    cB
    difss
    @0
    cA
    dfpss2
    mpbiran
    con2bii
    3bitri
end
