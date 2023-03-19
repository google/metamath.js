include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cpr.mm"
include "wss.mm"
include "prssg.mm"
include "elpwg.mm"
include "bi2anan9.mm"
include "bitr3d.mm"

theorem prsspwg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( { A , B } C_ ~P C <-> ( A C_ C /\ B C_ C ) ) )

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
    cpw
    #
    wcel
    #
    cB
    @2
    wcel
    #
    wa
    cA
    cB
    cpr
    @2
    wss
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    cA
    cB
    @2
    cV
    cW
    prssg
    @0
    @3
    @5
    @1
    @4
    @6
    cA
    cC
    cV
    elpwg
    cB
    cC
    cW
    elpwg
    bi2anan9
    bitr3d
end
