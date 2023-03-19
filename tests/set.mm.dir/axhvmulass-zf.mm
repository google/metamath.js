include "chlo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
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
include "hlmulass.mm"
include "mpan.mm"

theorem axhvmulass-zf
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ( ( A e. CC /\ B e. CC /\ C e. ~H ) -> ( ( A x. B ) .h C ) = ( A .h ( B .h C ) ) )

  proof
    cU
    chlo
    wcel
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    chil
    wcel
    w3a
    cA
    cB
    cmul
    co
    cC
    csm
    co
    cA
    cB
    cC
    csm
    co
    csm
    co
    wceq
    axhil.2
    cA
    cB
    cC
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
    hlmulass
    mpan
end
