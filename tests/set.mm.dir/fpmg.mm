include "wcel.mm"
include "wf.mm"
include "cpm.mm"
include "co.mm"
include "wa.mm"
include "wss.mm"
include "ssid.mm"
include "elpm2r.mm"
include "mpanr2.mm"
include "3impa.mm"
include "3com12.mm"

theorem fpmg
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ F : A --> B ) -> F e. ( B ^pm A ) )

  proof
    cB
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    cA
    cB
    cF
    wf
    #
    cF
    cB
    cA
    cpm
    co
    wcel
    #
    @0
    @1
    @2
    @3
    @0
    @1
    wa
    @2
    cA
    cA
    wss
    @3
    cA
    ssid
    cB
    cA
    cA
    cF
    cW
    cV
    elpm2r
    mpanr2
    3impa
    3com12
end
