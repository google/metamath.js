include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "csp.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlipcj.mm"
include "mp3an1.mm"

theorem axhis1-zf
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD
  assume axhfi.1: |- .ih = ( .iOLD ` U )


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A .ih B ) = ( * ` ( B .ih A ) ) )

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
    csp
    co
    cB
    cA
    csp
    co
    ccj
    cfv
    wceq
    axhil.2
    cA
    cB
    csp
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
    axhfi.1
    hlipcj
    mp3an1
end
