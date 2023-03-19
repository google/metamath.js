include "cmv.mm"
include "chil.mm"
include "cv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cmpt2.mm"
include "cnsb.mm"
include "cfv.mm"
include "df-hvsub.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "h2hva.mm"
include "h2hsm.mm"
include "eqid.mm"
include "nvmfval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem h2hvs
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume h2h.1: |- U = <. <. +h , .h >. , normh >.
  assume h2h.2: |- U e. NrmCVec
  assume h2h.4: |- ~H = ( BaseSet ` U )


  assert |- -h = ( -v ` U )

  proof
    cmv
    vx
    vy
    chil
    chil
    vx
    cv
    c1
    cneg
    vy
    cv
    csm
    co
    cva
    co
    cmpt2
    #
    cU
    cnsb
    cfv
    #
    vx
    vy
    df-hvsub
    cU
    cnv
    wcel
    @1
    @0
    wceq
    h2h.2
    vx
    vy
    csm
    cU
    cva
    @1
    chil
    h2h.4
    cU
    h2h.1
    h2h.2
    h2hva
    cU
    h2h.1
    h2h.2
    h2hsm
    @1
    eqid
    nvmfval
    ax-mp
    eqtr4i
end
