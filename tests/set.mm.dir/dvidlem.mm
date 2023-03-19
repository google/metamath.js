include "cc.mm"
include "cdv.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "cdm.mm"
include "dvfcn.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "dvbss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "wbr.mm"
include "reldv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cnt.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "simpr.mm"
include "ctop.mm"
include "wceq.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "ntrtop.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "cres.mm"
include "limcresi.mm"
include "ccncf.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "eqidd.mm"
include "cnmptlimc.mm"
include "sseldi.mm"
include "wne.mm"
include "eldifsn.mm"
include "3exp2.mm"
include "imp43.mm"
include "sylan2b.mm"
include "mpteq2dva.mm"
include "difss.mm"
include "resmpt.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "crest.mm"
include "restid.mm"
include "eqcomi.mm"
include "adantr.mm"
include "eldv.mm"
include "mpbir2and.mm"
include "releldm.mm"
include "sylancr.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "mpbii.mm"
include "ffn.mm"
include "syl.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "funbrfvb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"

theorem dvidlem
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cF: class F
  assume dvidlem.1: |- ( ph -> F : CC --> CC )
  assume dvidlem.2: |- ( ( ph /\ ( x e. CC /\ z e. CC /\ z =/= x ) ) -> ( ( ( F ` z ) - ( F ` x ) ) / ( z - x ) ) = B )
  assume dvidlem.3: |- B e. CC

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint ph x
  disjoint ph z
  assert |- ( ph -> ( CC _D F ) = ( CC X. { B } ) )

  proof
    wph
    vx
    cc
    cc
    cF
    cdv
    co
    #
    cc
    cB
    csn
    cxp
    #
    wph
    cc
    cc
    @0
    wf
    #
    @0
    cc
    wfn
    wph
    @0
    cdm
    #
    cc
    @0
    wf
    #
    @2
    cF
    dvfcn
    #
    wph
    @3
    cc
    cc
    @0
    wph
    @3
    cc
    wph
    cc
    cc
    cF
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    #
    dvidlem.1
    @8
    dvbss
    wph
    vx
    cc
    @3
    wph
    vx
    cv
    #
    cc
    wcel
    #
    @9
    @3
    wcel
    #
    wph
    @10
    wa
    #
    @0
    wrel
    @9
    cB
    @0
    wbr
    #
    @11
    cc
    cF
    reldv
    @12
    @13
    @9
    cc
    ccnfld
    ctopn
    cfv
    #
    cnt
    cfv
    cfv
    #
    wcel
    cB
    vz
    cc
    @9
    csn
    #
    cdif
    #
    vz
    cv
    #
    cF
    cfv
    @9
    cF
    cfv
    cmin
    co
    @18
    @9
    cmin
    co
    cdiv
    co
    #
    cmpt
    #
    @9
    climc
    co
    #
    wcel
    @12
    @9
    cc
    @15
    wph
    @10
    simpr
    #
    @14
    ctop
    wcel
    #
    @15
    cc
    wceq
    @14
    @14
    eqid
    #
    cnfldtop
    #
    @14
    cc
    cc
    @14
    @14
    @24
    cnfldtopon
    toponunii
    #
    ntrtop
    ax-mp
    syl6eleqr
    @12
    cB
    vz
    cc
    cB
    cmpt
    #
    @17
    cres
    #
    @9
    climc
    co
    #
    @21
    @12
    @27
    @9
    climc
    co
    @29
    cB
    @9
    @17
    @27
    limcresi
    @12
    vz
    cc
    @9
    cc
    cB
    cB
    @12
    cB
    cc
    wcel
    #
    @6
    @6
    @27
    cc
    cc
    ccncf
    co
    wcel
    @30
    @12
    dvidlem.3
    a1i
    @6
    @12
    @7
    a1i
    #
    @31
    vz
    cB
    cc
    cc
    cncfmptc
    syl3anc
    @22
    @18
    @9
    wceq
    cB
    eqidd
    cnmptlimc
    sseldi
    @12
    @20
    @28
    @9
    climc
    @12
    @20
    vz
    @17
    cB
    cmpt
    #
    @28
    @12
    vz
    @17
    @19
    cB
    @18
    @17
    wcel
    @12
    @18
    cc
    wcel
    #
    @18
    @9
    wne
    #
    wa
    @19
    cB
    wceq
    #
    @18
    cc
    @9
    eldifsn
    wph
    @10
    @33
    @34
    @35
    wph
    @10
    @33
    @34
    @35
    dvidlem.2
    3exp2
    imp43
    sylan2b
    mpteq2dva
    @17
    cc
    wss
    @28
    @32
    wceq
    cc
    @16
    difss
    vz
    cc
    @17
    cB
    resmpt
    ax-mp
    syl6eqr
    oveq1d
    eleqtrrd
    @12
    vz
    cc
    @9
    cB
    cc
    @14
    cF
    @20
    @14
    @14
    cc
    crest
    co
    #
    @14
    @23
    @36
    @14
    wceq
    @25
    @14
    ctop
    cc
    @26
    restid
    ax-mp
    eqcomi
    @24
    @20
    eqid
    @31
    wph
    cc
    cc
    cF
    wf
    @10
    dvidlem.1
    adantr
    @31
    eldv
    mpbir2and
    #
    @9
    cB
    @0
    releldm
    sylancr
    #
    ex
    ssrdv
    eqssd
    feq2d
    mpbii
    cc
    cc
    @0
    ffn
    syl
    @30
    @1
    cc
    wfn
    wph
    dvidlem.3
    cc
    cB
    cc
    fnconstg
    mp1i
    @12
    @9
    @0
    cfv
    #
    cB
    @9
    @1
    cfv
    #
    @12
    @39
    cB
    wceq
    #
    @13
    @37
    @12
    @0
    wfun
    #
    @11
    @41
    @13
    wb
    @4
    @42
    @12
    @5
    @3
    cc
    @0
    ffun
    mp1i
    @38
    @9
    cB
    @0
    funbrfvb
    syl2anc
    mpbird
    wph
    @30
    @10
    @40
    cB
    wceq
    @30
    wph
    dvidlem.3
    a1i
    cc
    cB
    @9
    cc
    fvconst2g
    sylan
    eqtr4d
    eqfnfvd
end
