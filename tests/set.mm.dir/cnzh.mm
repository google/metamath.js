include "ccnfld.mm"
include "czlm.mm"
include "cfv.mm"
include "cnlm.mm"
include "wcel.mm"
include "cngp.mm"
include "clmod.mm"
include "zring.mm"
include "cnrg.mm"
include "w3a.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "cabs.mm"
include "cz.mm"
include "cres.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "wral.mm"
include "cnnrg.mm"
include "eqid.mm"
include "zhmnrg.mm"
include "nrgngp.mm"
include "mp2b.mm"
include "cabl.mm"
include "crg.mm"
include "nrgring.mm"
include "ringabl.mm"
include "zlmlmod.mm"
include "mpbi.mm"
include "zringnrg.mm"
include "3pm3.2i.mm"
include "wa.mm"
include "simpl.mm"
include "zcnd.mm"
include "simpr.mm"
include "absmuld.mm"
include "cnfldmulg.mm"
include "fveq2d.mm"
include "fvres.mm"
include "adantr.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "rgen2.mm"
include "cnfldbas.mm"
include "zlmbas.mm"
include "cvv.mm"
include "cnm.mm"
include "cnfldex.mm"
include "cnfldnm.mm"
include "zlmnm.mm"
include "ax-mp.mm"
include "zlmvsca.mm"
include "csca.mm"
include "zlmsca.mm"
include "zringbas.mm"
include "zringnm.mm"
include "eqcomi.mm"
include "isnlm.mm"
include "mpbir2an.mm"

theorem cnzh
  let vx: setvar x
  let vz: setvar z


  assert |- ( ZMod ` CCfld ) e. NrmMod

  proof
    ccnfld
    czlm
    cfv
    #
    cnlm
    wcel
    @0
    cngp
    wcel
    #
    @0
    clmod
    wcel
    #
    zring
    cnrg
    wcel
    #
    w3a
    vz
    cv
    #
    vx
    cv
    #
    ccnfld
    cmg
    cfv
    #
    co
    #
    cabs
    cfv
    #
    @4
    cabs
    cz
    cres
    #
    cfv
    #
    @5
    cabs
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cc
    wral
    vz
    cz
    wral
    @1
    @2
    @3
    ccnfld
    cnrg
    wcel
    #
    @0
    cnrg
    wcel
    @1
    cnnrg
    ccnfld
    @0
    @0
    eqid
    #
    zhmnrg
    @0
    nrgngp
    mp2b
    ccnfld
    cabl
    wcel
    #
    @2
    @14
    ccnfld
    crg
    wcel
    @16
    cnnrg
    ccnfld
    nrgring
    ccnfld
    ringabl
    mp2b
    ccnfld
    @0
    @15
    zlmlmod
    mpbi
    zringnrg
    3pm3.2i
    @13
    vz
    vx
    cz
    cc
    @4
    cz
    wcel
    #
    @5
    cc
    wcel
    #
    wa
    #
    @4
    @5
    cmul
    co
    #
    cabs
    cfv
    @4
    cabs
    cfv
    #
    @11
    cmul
    co
    @8
    @12
    @19
    @4
    @5
    @19
    @4
    @17
    @18
    simpl
    zcnd
    @17
    @18
    simpr
    absmuld
    @19
    @7
    @20
    cabs
    @4
    @5
    cnfldmulg
    fveq2d
    @19
    @10
    @21
    @11
    cmul
    @17
    @10
    @21
    wceq
    @18
    @4
    cz
    cabs
    fvres
    adantr
    oveq1d
    3eqtr4d
    rgen2
    vz
    vx
    @9
    @6
    zring
    cz
    cabs
    cc
    @0
    cc
    ccnfld
    @0
    @15
    cnfldbas
    zlmbas
    ccnfld
    cvv
    wcel
    #
    cabs
    @0
    cnm
    cfv
    wceq
    cnfldex
    ccnfld
    cabs
    cvv
    @0
    @15
    cnfldnm
    zlmnm
    ax-mp
    @6
    ccnfld
    @0
    @15
    @6
    eqid
    zlmvsca
    @22
    zring
    @0
    csca
    cfv
    wceq
    cnfldex
    ccnfld
    cvv
    @0
    @15
    zlmsca
    ax-mp
    zringbas
    zring
    cnm
    cfv
    @9
    zringnm
    eqcomi
    isnlm
    mpbir2an
end
