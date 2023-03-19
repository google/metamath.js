include "csn.mm"
include "wss.mm"
include "wa.mm"
include "cun.mm"
include "wcel.mm"
include "cpr.mm"
include "unss.mm"
include "snss.mm"
include "anbi12i.mm"
include "df-pr.mm"
include "sseq1i.mm"
include "3bitr4i.mm"

theorem prssOLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume prss.1: |- A e. _V
  assume prss.2: |- B e. _V


  assert |- ( ( A e. C /\ B e. C ) <-> { A , B } C_ C )

  proof
    cA
    csn
    #
    cC
    wss
    #
    cB
    csn
    #
    cC
    wss
    #
    wa
    @0
    @2
    cun
    #
    cC
    wss
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    wa
    cA
    cB
    cpr
    #
    cC
    wss
    @0
    @2
    cC
    unss
    @5
    @1
    @6
    @3
    cA
    cC
    prss.1
    snss
    cB
    cC
    prss.2
    snss
    anbi12i
    @7
    @4
    cC
    cA
    cB
    df-pr
    sseq1i
    3bitr4i
end
