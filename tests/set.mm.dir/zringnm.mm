include "ccnfld.mm"
include "cmnd.mm"
include "wcel.mm"
include "cc0.mm"
include "cz.mm"
include "cc.mm"
include "wss.mm"
include "zring.mm"
include "cnm.mm"
include "cfv.mm"
include "cabs.mm"
include "cres.mm"
include "wceq.mm"
include "crg.mm"
include "cnring.mm"
include "ringmnd.mm"
include "ax-mp.mm"
include "0z.mm"
include "zsscn.mm"
include "w3a.mm"
include "df-zring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cnfldnm.mm"
include "ressnm.mm"
include "eqcomd.mm"
include "mp3an.mm"

theorem zringnm



  assert |- ( norm ` ZZring ) = ( abs |` ZZ )

  proof
    ccnfld
    cmnd
    wcel
    #
    cc0
    cz
    wcel
    #
    cz
    cc
    wss
    #
    zring
    cnm
    cfv
    #
    cabs
    cz
    cres
    #
    wceq
    ccnfld
    crg
    wcel
    @0
    cnring
    ccnfld
    ringmnd
    ax-mp
    0z
    zsscn
    @0
    @1
    @2
    w3a
    @4
    @3
    cz
    cc
    ccnfld
    zring
    cabs
    cc0
    df-zring
    cnfldbas
    cnfld0
    cnfldnm
    ressnm
    eqcomd
    mp3an
end
