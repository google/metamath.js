include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "cpw.mm"
include "prssg.mm"
include "prex.mm"
include "elpw.mm"
include "syl6bbr.mm"

theorem prelpw
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( ( A e. C /\ B e. C ) <-> { A , B } e. ~P C ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cC
    wcel
    cB
    cC
    wcel
    wa
    cA
    cB
    cpr
    #
    cC
    wss
    @0
    cC
    cpw
    wcel
    cA
    cB
    cC
    cV
    cW
    prssg
    @0
    cC
    cA
    cB
    prex
    elpw
    syl6bbr
end
