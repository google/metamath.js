include "ccnfld.mm"
include "cuss.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmetu.mm"
include "cc.mm"
include "cxp.mm"
include "cuni.mm"
include "wceq.mm"
include "cust.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cc0.mm"
include "0cn.mm"
include "ne0ii.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "xmetpsmet.mm"
include "ax-mp.mm"
include "metuust.mm"
include "mp2an.mm"
include "ustuni.mm"
include "eqcomi.mm"
include "cnfldbas.mm"
include "cnfldunif.mm"
include "ussid.mm"
include "eqtr4i.mm"

theorem cnflduss
  let cU: class U
  assume cnflduss.1: |- U = ( UnifSt ` CCfld )


  assert |- U = ( metUnif ` ( abs o. - ) )

  proof
    cU
    ccnfld
    cuss
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmetu
    cfv
    #
    cnflduss.1
    cc
    cc
    cxp
    #
    @2
    cuni
    #
    wceq
    @2
    @0
    wceq
    @4
    @3
    @2
    cc
    cust
    cfv
    wcel
    #
    @4
    @3
    wceq
    cc
    c0
    wne
    @1
    cc
    cpsmet
    cfv
    wcel
    #
    @5
    cc0
    cc
    0cn
    ne0ii
    @1
    cc
    cxmt
    cfv
    wcel
    @6
    cnxmet
    @1
    cc
    xmetpsmet
    ax-mp
    @1
    cc
    metuust
    mp2an
    @2
    cc
    ustuni
    ax-mp
    eqcomi
    cc
    @2
    ccnfld
    cnfldbas
    cnfldunif
    ussid
    ax-mp
    eqtr4i
end
