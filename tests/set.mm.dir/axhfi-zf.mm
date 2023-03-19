include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "cxp.mm"
include "cc.mm"
include "csp.mm"
include "wf.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlipf.mm"
include "ax-mp.mm"

theorem axhfi-zf
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD
  assume axhfi.1: |- .ih = ( .iOLD ` U )


  assert |- .ih : ( ~H X. ~H ) --> CC

  proof
    cU
    chlo
    wcel
    chil
    chil
    cxp
    cc
    csp
    wf
    axhil.2
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
    hlipf
    ax-mp
end
