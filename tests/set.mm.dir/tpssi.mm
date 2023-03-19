include "wcel.mm"
include "w3a.mm"
include "ctp.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "wss.mm"
include "prssi.mm"
include "3adant3.mm"
include "snssi.mm"
include "3ad2ant3.mm"
include "unssd.mm"
include "syl5eqss.mm"

theorem tpssi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. D /\ B e. D /\ C e. D ) -> { A , B , C } C_ D )

  proof
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
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    cD
    cA
    cB
    cC
    df-tp
    @3
    @4
    @5
    cD
    @0
    @1
    @4
    cD
    wss
    @2
    cA
    cB
    cD
    prssi
    3adant3
    @2
    @0
    @5
    cD
    wss
    @1
    cC
    cD
    snssi
    3ad2ant3
    unssd
    syl5eqss
end
