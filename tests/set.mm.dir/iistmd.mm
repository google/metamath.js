include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "ctmd.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "csubmnd.mm"
include "cnrg.mm"
include "ctrg.mm"
include "cnnrg.mm"
include "nrgtrg.mm"
include "eqid.mm"
include "trgtmd.mm"
include "mp2b.mm"
include "cc.mm"
include "wss.mm"
include "cv.mm"
include "cmul.mm"
include "wral.mm"
include "unitsscn.mm"
include "1elunit.mm"
include "iimulcl.mm"
include "rgen2a.mm"
include "cmnd.mm"
include "w3a.mm"
include "wb.mm"
include "crg.mm"
include "nrgring.mm"
include "ringmgp.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "issubm.mm"
include "ax-mp.mm"
include "mpbir3an.mm"
include "submtmd.mm"
include "mp2an.mm"

theorem iistmd
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume df-iis: |- I = ( ( mulGrp ` CCfld ) |`s ( 0 [,] 1 ) )


  assert |- I e. TopMnd

  proof
    ccnfld
    cmgp
    cfv
    #
    ctmd
    wcel
    #
    cc0
    c1
    cicc
    co
    #
    @0
    csubmnd
    cfv
    wcel
    #
    cI
    ctmd
    wcel
    ccnfld
    cnrg
    wcel
    #
    ccnfld
    ctrg
    wcel
    @1
    cnnrg
    ccnfld
    nrgtrg
    ccnfld
    @0
    @0
    eqid
    #
    trgtmd
    mp2b
    @3
    @2
    cc
    wss
    #
    c1
    @2
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    @2
    wcel
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    unitsscn
    1elunit
    @10
    vx
    vy
    @2
    @8
    @9
    iimulcl
    rgen2a
    @0
    cmnd
    wcel
    #
    @3
    @6
    @7
    @11
    w3a
    wb
    @4
    ccnfld
    crg
    wcel
    @12
    cnnrg
    ccnfld
    nrgring
    ccnfld
    @0
    @5
    ringmgp
    mp2b
    vx
    vy
    cc
    cmul
    @2
    @0
    c1
    cc
    ccnfld
    @0
    @5
    cnfldbas
    mgpbas
    ccnfld
    c1
    @0
    @5
    cnfld1
    ringidval
    ccnfld
    cmul
    @0
    @5
    cnfldmul
    mgpplusg
    issubm
    ax-mp
    mpbir3an
    @2
    @0
    cI
    df-iis
    submtmd
    mp2an
end
