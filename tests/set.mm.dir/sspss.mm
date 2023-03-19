include "wss.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "dfpss2.mm"
include "simplbi2.mm"
include "con1d.mm"
include "orrd.mm"
include "pssss.mm"
include "eqimss.mm"
include "jaoi.mm"
include "impbii.mm"

theorem sspss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( A C. B \/ A = B ) )

  proof
    cA
    cB
    wss
    #
    cA
    cB
    wpss
    #
    cA
    cB
    wceq
    #
    wo
    @0
    @1
    @2
    @0
    @2
    @1
    @1
    @0
    @2
    wn
    cA
    cB
    dfpss2
    simplbi2
    con1d
    orrd
    @1
    @0
    @2
    cA
    cB
    pssss
    cA
    cB
    eqimss
    jaoi
    impbii
end
