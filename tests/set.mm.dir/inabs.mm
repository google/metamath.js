include "cun.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "ssun1.mm"
include "df-ss.mm"
include "mpbi.mm"

theorem inabs
  let cA: class A
  let cB: class B


  assert |- ( A i^i ( A u. B ) ) = A

  proof
    cA
    cA
    cB
    cun
    #
    wss
    cA
    @0
    cin
    cA
    wceq
    cA
    cB
    ssun1
    cA
    @0
    df-ss
    mpbi
end
