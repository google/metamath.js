include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cc.mm"
include "cxmt.mm"
include "wcel.mm"
include "ctopon.mm"
include "wceq.mm"
include "cnxmet.mm"
include "eqid.mm"
include "mopntopon.mm"
include "cnfldbas.mm"
include "cnfldtset.mm"
include "topontopn.mm"
include "mp2b.mm"
include "eqtr4i.mm"

theorem cnfldtopn
  let cJ: class J
  assume cnfldtopn.1: |- J = ( TopOpen ` CCfld )


  assert |- J = ( MetOpen ` ( abs o. - ) )

  proof
    cJ
    ccnfld
    ctopn
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    #
    cnfldtopn.1
    @1
    cc
    cxmt
    cfv
    wcel
    @2
    cc
    ctopon
    cfv
    wcel
    @2
    @0
    wceq
    cnxmet
    @1
    @2
    cc
    @2
    eqid
    mopntopon
    cc
    @2
    ccnfld
    cnfldbas
    cnfldtset
    topontopn
    mp2b
    eqtr4i
end
