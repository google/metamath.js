include "chlo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "csp.mm"
include "cmul.mm"
include "wceq.mm"
include "cva.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlnvi.mm"
include "h2hsm.mm"
include "hlipass.mm"
include "mpan.mm"

theorem axhis3-zf
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD
  assume axhfi.1: |- .ih = ( .iOLD ` U )


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( ( A .h B ) .ih C ) = ( A x. ( B .ih C ) ) )

  proof
    cU
    chlo
    wcel
    cA
    cc
    wcel
    cB
    chil
    wcel
    cC
    chil
    wcel
    w3a
    cA
    cB
    csm
    co
    cC
    csp
    co
    cA
    cB
    cC
    csp
    co
    cmul
    co
    wceq
    axhil.2
    cA
    cB
    cC
    csp
    csm
    cU
    chil
    chil
    cva
    csm
    cop
    cno
    cop
    #
    cba
    cfv
    cU
    cba
    cfv
    df-hba
    cU
    @0
    cba
    axhil.1
    fveq2i
    eqtr4i
    cU
    axhil.1
    cU
    axhil.2
    hlnvi
    h2hsm
    axhfi.1
    hlipass
    mpan
end
