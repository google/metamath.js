include "ccnfld.mm"
include "crglmod.mm"
include "cfv.mm"
include "cclm.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "ccvs.mm"
include "eqid.mm"
include "cncvs.mm"
include "id.mm"
include "cvsclm.mm"
include "ax-mp.mm"
include "cbs.mm"
include "cnrbas.mm"
include "eqcomi.mm"
include "cvv.mm"
include "csca.mm"
include "cnfldex.mm"
include "rlmsca.mm"
include "cmulr.mm"
include "cvsca.mm"
include "cnfldmul.mm"
include "rlmvsca.mm"
include "eqtri.mm"
include "cnfldbas.mm"
include "clmvsass.mm"
include "mpan.mm"

theorem cnncvsmulassdemo
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A x. B ) x. C ) = ( A x. ( B x. C ) ) )

  proof
    ccnfld
    crglmod
    cfv
    #
    cclm
    wcel
    #
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    w3a
    cA
    cB
    cmul
    co
    cC
    cmul
    co
    cA
    cB
    cC
    cmul
    co
    cmul
    co
    wceq
    @0
    ccvs
    wcel
    #
    @1
    @0
    @0
    eqid
    #
    cncvs
    @2
    @0
    @2
    id
    cvsclm
    ax-mp
    cA
    cB
    cmul
    ccnfld
    cc
    cc
    @0
    cC
    @0
    cbs
    cfv
    cc
    @0
    @3
    cnrbas
    eqcomi
    ccnfld
    cvv
    wcel
    ccnfld
    @0
    csca
    cfv
    wceq
    cnfldex
    ccnfld
    cvv
    rlmsca
    ax-mp
    cmul
    ccnfld
    cmulr
    cfv
    @0
    cvsca
    cfv
    cnfldmul
    ccnfld
    rlmvsca
    eqtri
    ccnfld
    cbs
    cfv
    #
    cc
    cc
    @4
    cnfldbas
    eqcomi
    eqcomi
    clmvsass
    mpan
end
