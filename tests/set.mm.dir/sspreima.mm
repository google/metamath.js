include "wfun.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "wceq.mm"
include "inpreima.mm"
include "df-ss.mm"
include "biimpi.mm"
include "imaeq2d.mm"
include "sylan9req.mm"
include "sylibr.mm"

theorem sspreima
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A C_ B ) -> ( `' F " A ) C_ ( `' F " B ) )

  proof
    cF
    wfun
    #
    cA
    cB
    wss
    #
    wa
    cF
    ccnv
    #
    cA
    cima
    #
    @2
    cB
    cima
    #
    cin
    #
    @3
    wceq
    @3
    @4
    wss
    @0
    @1
    @5
    @2
    cA
    cB
    cin
    #
    cima
    @3
    cA
    cB
    cF
    inpreima
    @1
    @6
    cA
    @2
    @1
    @6
    cA
    wceq
    cA
    cB
    df-ss
    biimpi
    imaeq2d
    sylan9req
    @3
    @4
    df-ss
    sylibr
end
