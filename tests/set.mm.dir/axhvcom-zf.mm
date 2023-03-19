include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlnvi.mm"
include "h2hva.mm"
include "hlcom.mm"
include "mp3an1.mm"

theorem axhvcom-zf
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A +h B ) = ( B +h A ) )

  proof
    cU
    chlo
    wcel
    cA
    chil
    wcel
    cB
    chil
    wcel
    cA
    cB
    cva
    co
    cB
    cA
    cva
    co
    wceq
    axhil.2
    cA
    cB
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
    h2hva
    hlcom
    mp3an1
end
