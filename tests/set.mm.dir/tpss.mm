include "cpr.mm"
include "wss.mm"
include "csn.mm"
include "wa.mm"
include "cun.mm"
include "wcel.mm"
include "w3a.mm"
include "ctp.mm"
include "unss.mm"
include "df-3an.mm"
include "prss.mm"
include "snss.mm"
include "anbi12i.mm"
include "bitri.mm"
include "df-tp.mm"
include "sseq1i.mm"
include "3bitr4i.mm"

theorem tpss
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume tpss.1: |- A e. _V
  assume tpss.2: |- B e. _V
  assume tpss.3: |- C e. _V


  assert |- ( ( A e. D /\ B e. D /\ C e. D ) <-> { A , B , C } C_ D )

  proof
    cA
    cB
    cpr
    #
    cD
    wss
    #
    cC
    csn
    #
    cD
    wss
    #
    wa
    #
    @0
    @2
    cun
    #
    cD
    wss
    cA
    cD
    wcel
    #
    cB
    cD
    wcel
    #
    cC
    cD
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    ctp
    #
    cD
    wss
    @0
    @2
    cD
    unss
    @9
    @6
    @7
    wa
    #
    @8
    wa
    @4
    @6
    @7
    @8
    df-3an
    @11
    @1
    @8
    @3
    cA
    cB
    cD
    tpss.1
    tpss.2
    prss
    cC
    cD
    tpss.3
    snss
    anbi12i
    bitri
    @10
    @5
    cD
    cA
    cB
    cC
    df-tp
    sseq1i
    3bitr4i
end
