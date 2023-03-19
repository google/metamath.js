include "cc.mm"
include "wss.mm"
include "wf.mm"
include "w3a.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "ccncf.mm"
include "wcel.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "simpl2.mm"
include "eqid.mm"
include "dvcnp2.mm"
include "ralrimiva.mm"
include "raleq.mm"
include "biimpd.mm"
include "mpan9.mm"
include "ctopon.mm"
include "wb.mm"
include "cnfldtopon.mm"
include "simpl3.mm"
include "simpl1.mm"
include "sstrd.mm"
include "resttopon.mm"
include "sylancr.mm"
include "cncnp.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "ssid.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "eleqtrrd.mm"

theorem dvcn
  let cA: class A
  let cS: class S
  let cF: class F
  let vx: setvar x


  assert |- ( ( ( S C_ CC /\ F : A --> CC /\ A C_ S ) /\ dom ( S _D F ) = A ) -> F e. ( A -cn-> CC ) )

  proof
    cS
    cc
    wss
    #
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    #
    w3a
    #
    cS
    cF
    cdv
    co
    cdm
    #
    cA
    wceq
    #
    wa
    #
    cF
    ccnfld
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    @7
    ccn
    co
    #
    cA
    cc
    ccncf
    co
    #
    @6
    cF
    @9
    wcel
    #
    @1
    cF
    vx
    cv
    #
    @8
    @7
    ccnp
    co
    cfv
    wcel
    #
    vx
    cA
    wral
    #
    @0
    @1
    @2
    @5
    simpl2
    @3
    @13
    vx
    @4
    wral
    #
    @5
    @14
    @3
    @13
    vx
    @4
    cA
    @12
    cS
    cF
    @8
    @7
    @8
    eqid
    #
    @7
    eqid
    #
    dvcnp2
    ralrimiva
    @5
    @15
    @14
    @13
    vx
    @4
    cA
    raleq
    biimpd
    mpan9
    @6
    @8
    cA
    ctopon
    cfv
    wcel
    #
    @7
    cc
    ctopon
    cfv
    #
    wcel
    #
    @11
    @1
    @14
    wa
    wb
    @6
    @20
    cA
    cc
    wss
    #
    @18
    @7
    @17
    cnfldtopon
    #
    @6
    cA
    cS
    cc
    @0
    @1
    @2
    @5
    simpl3
    @0
    @1
    @2
    @5
    simpl1
    sstrd
    #
    cA
    @7
    cc
    resttopon
    sylancr
    @22
    vx
    cF
    @8
    @7
    cA
    cc
    cncnp
    sylancl
    mpbir2and
    @6
    @21
    cc
    cc
    wss
    @10
    @9
    wceq
    @23
    cc
    ssid
    cA
    cc
    @7
    @8
    @7
    @17
    @16
    @7
    cc
    crest
    co
    #
    @7
    @20
    @24
    @7
    wceq
    @22
    @7
    @19
    cc
    cc
    @7
    @22
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    sylancl
    eleqtrrd
end
