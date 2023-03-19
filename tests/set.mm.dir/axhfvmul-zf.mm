include "chlo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "cxp.mm"
include "csm.mm"
include "wf.mm"
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
include "hlmulf.mm"
include "ax-mp.mm"

theorem axhfvmul-zf
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- .h : ( CC X. ~H ) --> ~H

  proof
    cU
    chlo
    wcel
    cc
    chil
    cxp
    chil
    csm
    wf
    axhil.2
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
    hlmulf
    ax-mp
end
