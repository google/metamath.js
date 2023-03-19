include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wss.mm"
include "cpr.mm"
include "snssg.mm"
include "bi2anan9.mm"
include "cun.mm"
include "unss.mm"
include "df-pr.mm"
include "sseq1i.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem prssg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
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
    #
    cA
    cB
    cpr
    #
    cC
    wss
    #
    @0
    @2
    @5
    @1
    @3
    @7
    cA
    cC
    cV
    snssg
    cB
    cC
    cW
    snssg
    bi2anan9
    @8
    @4
    @6
    cun
    #
    cC
    wss
    @10
    @4
    @6
    cC
    unss
    @9
    @11
    cC
    cA
    cB
    df-pr
    sseq1i
    bitr4i
    syl6bb
end
