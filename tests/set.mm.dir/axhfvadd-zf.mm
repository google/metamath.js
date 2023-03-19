include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "cxp.mm"
include "cva.mm"
include "wf.mm"
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
include "hladdf.mm"
include "ax-mp.mm"

theorem axhfvadd-zf
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- +h : ( ~H X. ~H ) --> ~H

  proof
    cU
    chlo
    wcel
    chil
    chil
    cxp
    chil
    cva
    wf
    axhil.2
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
    hladdf
    ax-mp
end
