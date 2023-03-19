include "chlo.mm"
include "wcel.mm"
include "c0v.mm"
include "chil.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "cn0v.mm"
include "df-h0v.mm"
include "hl0cl.mm"
include "ax-mp.mm"

theorem axhv0cl-zf
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- 0h e. ~H

  proof
    cU
    chlo
    wcel
    c0v
    chil
    wcel
    axhil.2
    cU
    chil
    c0v
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
    c0v
    @0
    cn0v
    cfv
    cU
    cn0v
    cfv
    df-h0v
    cU
    @0
    cn0v
    axhil.1
    fveq2i
    eqtr4i
    hl0cl
    ax-mp
end
