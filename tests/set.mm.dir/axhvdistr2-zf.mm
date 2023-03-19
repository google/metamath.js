include "chlo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "csm.mm"
include "cva.mm"
include "wceq.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlnvi.mm"
include "h2hva.mm"
include "h2hsm.mm"
include "hldir.mm"
include "mpan.mm"

theorem axhvdistr2-zf
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ( ( A e. CC /\ B e. CC /\ C e. ~H ) -> ( ( A + B ) .h C ) = ( ( A .h C ) +h ( B .h C ) ) )

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
    caddc
    co
    cC
    csm
    co
    cA
    cC
    csm
    co
    cB
    cC
    csm
    co
    cva
    co
    wceq
    axhil.2
    cA
    cB
    cC
    csm
    cU
    cva
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
    #
    h2hva
    cU
    axhil.1
    @1
    h2hsm
    hldir
    mpan
end
