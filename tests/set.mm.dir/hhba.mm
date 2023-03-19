include "chil.mm"
include "cva.mm"
include "crn.mm"
include "cba.mm"
include "cfv.mm"
include "cablo.mm"
include "wcel.mm"
include "cgr.mm"
include "hilablo.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "grporn.mm"
include "eqid.mm"
include "hhva.mm"
include "bafval.mm"
include "eqtr4i.mm"

theorem hhba
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- ~H = ( BaseSet ` U )

  proof
    chil
    cva
    crn
    cU
    cba
    cfv
    #
    cva
    chil
    cva
    cablo
    wcel
    cva
    cgr
    wcel
    hilablo
    cva
    ablogrpo
    ax-mp
    chil
    chil
    cxp
    chil
    cva
    ax-hfvadd
    fdmi
    grporn
    cU
    cva
    @0
    @0
    eqid
    cU
    hhnv.1
    hhva
    bafval
    eqtr4i
end
