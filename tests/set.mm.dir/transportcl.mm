include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "ctransport.mm"
include "co.mm"
include "cv.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "crio.mm"
include "fvtransport.mm"
include "wreu.mm"
include "segconeu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem transportcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vr: setvar r


  assert |- ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\ C =/= D ) ) -> ( <. A , B >. TransportTo <. C , D >. ) e. ( EE ` N ) )

  proof
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    wa
    cC
    @0
    wcel
    cD
    @0
    wcel
    wa
    cC
    cD
    wne
    w3a
    wa
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    ctransport
    co
    cD
    cC
    vr
    cv
    #
    cop
    cbtwn
    wbr
    cD
    @3
    cop
    @2
    ccgr
    wbr
    wa
    #
    vr
    @0
    crio
    #
    @0
    cA
    cB
    cC
    cD
    cN
    vr
    fvtransport
    @1
    @4
    vr
    @0
    wreu
    @5
    @0
    wcel
    cA
    cB
    cC
    cD
    cN
    vr
    segconeu
    @4
    vr
    @0
    riotacl
    syl
    eqeltrd
end
