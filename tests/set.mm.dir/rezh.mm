include "crefld.mm"
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
include "cvsca.mm"
include "co.mm"
include "cabs.mm"
include "cr.mm"
include "cres.mm"
include "cz.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cnnrg.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "df-refld.mm"
include "subrgnrg.mm"
include "mp2an.mm"
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
include "recnd.mm"
include "absmuld.mm"
include "cmg.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "zlmvsca.mm"
include "eqcomi.mm"
include "subgmulg.mm"
include "mp3an1.mm"
include "cc.mm"
include "cnfldmulg.mm"
include "syldan.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "zre.mm"
include "remulcl.mm"
include "fvres.mm"
include "syl.mm"
include "sylan.mm"
include "eqtrd.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "rgen2.mm"
include "rebase.mm"
include "zlmbas.mm"
include "cvv.mm"
include "cnm.mm"
include "ccusp.mm"
include "recusp.mm"
include "elexi.mm"
include "cmnd.mm"
include "cc0.mm"
include "wss.mm"
include "cnring.mm"
include "ringmnd.mm"
include "0re.mm"
include "ax-resscn.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cnfldnm.mm"
include "ressnm.mm"
include "mp3an.mm"
include "zlmnm.mm"
include "csca.mm"
include "zlmsca.mm"
include "zringbas.mm"
include "zringnm.mm"
include "isnlm.mm"
include "mpbir2an.mm"

theorem rezh
  let vx: setvar x
  let vz: setvar z


  assert |- ( ZMod ` RRfld ) e. NrmMod

  proof
    crefld
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
    @0
    cvsca
    cfv
    #
    co
    #
    cabs
    cr
    cres
    #
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
    @8
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cr
    wral
    vz
    cz
    wral
    @1
    @2
    @3
    crefld
    cnrg
    wcel
    #
    @0
    cnrg
    wcel
    @1
    ccnfld
    cnrg
    wcel
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @15
    cnnrg
    @16
    crefld
    cdr
    wcel
    resubdrg
    simpli
    #
    cr
    ccnfld
    crefld
    df-refld
    subrgnrg
    mp2an
    #
    crefld
    @0
    @0
    eqid
    #
    zhmnrg
    @0
    nrgngp
    mp2b
    crefld
    cabl
    wcel
    #
    @2
    @15
    crefld
    crg
    wcel
    @20
    @18
    crefld
    nrgring
    crefld
    ringabl
    mp2b
    crefld
    @0
    @19
    zlmlmod
    mpbi
    zringnrg
    3pm3.2i
    @14
    vz
    vx
    cz
    cr
    @4
    cz
    wcel
    #
    @5
    cr
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
    #
    @4
    cabs
    cfv
    #
    @5
    cabs
    cfv
    #
    cmul
    co
    @9
    @13
    @23
    @4
    @5
    @23
    @4
    @21
    @22
    simpl
    zcnd
    @23
    @5
    @21
    @22
    simpr
    recnd
    #
    absmuld
    @23
    @9
    @24
    @8
    cfv
    #
    @25
    @23
    @7
    @24
    @8
    @23
    @4
    @5
    ccnfld
    cmg
    cfv
    #
    co
    #
    @7
    @24
    cr
    ccnfld
    csubg
    cfv
    wcel
    #
    @21
    @22
    @31
    @7
    wceq
    @16
    @32
    @17
    cr
    ccnfld
    subrgsubg
    ax-mp
    cr
    @6
    @30
    ccnfld
    crefld
    @4
    @5
    @30
    eqid
    df-refld
    crefld
    cmg
    cfv
    #
    @6
    @33
    crefld
    @0
    @19
    @33
    eqid
    zlmvsca
    eqcomi
    subgmulg
    mp3an1
    @21
    @22
    @5
    cc
    wcel
    @31
    @24
    wceq
    @28
    @4
    @5
    cnfldmulg
    syldan
    eqtr3d
    fveq2d
    @21
    @4
    cr
    wcel
    #
    @22
    @29
    @25
    wceq
    #
    @4
    zre
    @34
    @22
    wa
    @24
    cr
    wcel
    @35
    @4
    @5
    remulcl
    @24
    cr
    cabs
    fvres
    syl
    sylan
    eqtrd
    @21
    @22
    @11
    @26
    @12
    @27
    cmul
    @4
    cz
    cabs
    fvres
    @5
    cr
    cabs
    fvres
    oveqan12d
    3eqtr4d
    rgen2
    vz
    vx
    @10
    @6
    zring
    cz
    @8
    cr
    @0
    cr
    crefld
    @0
    @19
    rebase
    zlmbas
    crefld
    cvv
    wcel
    #
    @8
    @0
    cnm
    cfv
    wceq
    crefld
    ccusp
    recusp
    elexi
    #
    crefld
    @8
    cvv
    @0
    @19
    ccnfld
    cmnd
    wcel
    #
    cc0
    cr
    wcel
    cr
    cc
    wss
    @8
    crefld
    cnm
    cfv
    wceq
    ccnfld
    crg
    wcel
    @38
    cnring
    ccnfld
    ringmnd
    ax-mp
    0re
    ax-resscn
    cr
    cc
    ccnfld
    crefld
    cabs
    cc0
    df-refld
    cnfldbas
    cnfld0
    cnfldnm
    ressnm
    mp3an
    zlmnm
    ax-mp
    @6
    eqid
    @36
    zring
    @0
    csca
    cfv
    wceq
    @37
    crefld
    cvv
    @0
    @19
    zlmsca
    ax-mp
    zringbas
    zring
    cnm
    cfv
    @10
    zringnm
    eqcomi
    isnlm
    mpbir2an
end
