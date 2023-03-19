include "cres.mm"
include "climc.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "limcrcl.mm"
include "simp3d.mm"
include "limccl.mm"
include "sseli.mm"
include "jca.mm"
include "a1i.mm"
include "wb.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnp.mm"
include "crest.mm"
include "ctop.mm"
include "cuni.mm"
include "cnt.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "adantr.mm"
include "simprl.mm"
include "snssd.mm"
include "unssd.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "syl.mm"
include "unss1.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "wo.mm"
include "elun.mm"
include "simplrr.mm"
include "ffvelrnda.mm"
include "ifcld.mm"
include "elsni.mm"
include "adantl.mm"
include "iftrued.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "toponunii.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "ellimc.mm"
include "fssresd.mm"
include "sstrd.mm"
include "resmptd.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "wn.mm"
include "pm5.61.mm"
include "fvres.mm"
include "sylbi.mm"
include "ifeq2da.mm"
include "mpteq2ia.mm"
include "syl6reqr.mm"
include "oveq1i.mm"
include "cvv.mm"
include "cnex.mm"
include "ssex.mm"
include "restabs.mm"
include "syl3anc.mm"
include "syl5req.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleq12d.mm"
include "bitrd.mm"
include "3bitr4rd.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem limcres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let vz: setvar z
  let vx: setvar x
  assume limcres.f: |- ( ph -> F : A --> CC )
  assume limcres.c: |- ( ph -> C C_ A )
  assume limcres.a: |- ( ph -> A C_ CC )
  assume limcres.k: |- K = ( TopOpen ` CCfld )
  assume limcres.j: |- J = ( K |`t ( A u. { B } ) )
  assume limcres.i: |- ( ph -> B e. ( ( int ` J ) ` ( C u. { B } ) ) )


  assert |- ( ph -> ( ( F |` C ) limCC B ) = ( F limCC B ) )

  proof
    wph
    vx
    cF
    cC
    cres
    #
    cB
    climc
    co
    #
    cF
    cB
    climc
    co
    #
    wph
    cB
    cc
    wcel
    #
    vx
    cv
    #
    cc
    wcel
    #
    wa
    #
    @4
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    @7
    @6
    wi
    wph
    @7
    @3
    @5
    @7
    @0
    cdm
    #
    cc
    @0
    wf
    @9
    cc
    wss
    @3
    cB
    @4
    @0
    limcrcl
    simp3d
    @1
    cc
    @4
    cB
    @0
    limccl
    sseli
    jca
    a1i
    @8
    @6
    wi
    wph
    @8
    @3
    @5
    @8
    cF
    cdm
    #
    cc
    cF
    wf
    @10
    cc
    wss
    @3
    cB
    @4
    cF
    limcrcl
    simp3d
    @2
    cc
    @4
    cB
    cF
    limccl
    sseli
    jca
    a1i
    wph
    @6
    @7
    @8
    wb
    wph
    @6
    wa
    #
    vz
    cA
    cB
    csn
    #
    cun
    #
    vz
    cv
    #
    cB
    wceq
    #
    @4
    @14
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    @18
    cC
    @12
    cun
    #
    cres
    #
    cB
    cJ
    @20
    crest
    co
    #
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @8
    @7
    @11
    cJ
    ctop
    wcel
    #
    @20
    cJ
    cuni
    #
    wss
    cB
    @20
    cJ
    cnt
    cfv
    cfv
    wcel
    #
    @27
    cc
    @18
    wf
    #
    @19
    @25
    wb
    @11
    cJ
    @13
    ctopon
    cfv
    #
    wcel
    #
    @26
    @11
    cJ
    cK
    @13
    crest
    co
    #
    @30
    limcres.j
    @11
    cK
    cc
    ctopon
    cfv
    #
    wcel
    #
    @13
    cc
    wss
    #
    @32
    @30
    wcel
    cK
    limcres.k
    cnfldtopon
    #
    @11
    cA
    @12
    cc
    wph
    cA
    cc
    wss
    @6
    limcres.a
    adantr
    #
    @11
    cB
    cc
    wph
    @3
    @5
    simprl
    #
    snssd
    unssd
    #
    @13
    cK
    cc
    resttopon
    sylancr
    syl5eqel
    #
    @13
    cJ
    topontop
    syl
    @11
    @20
    @13
    @27
    @11
    cC
    cA
    wss
    #
    @20
    @13
    wss
    #
    wph
    @41
    @6
    limcres.c
    adantr
    #
    cC
    cA
    @12
    unss1
    syl
    #
    @11
    @31
    @13
    @27
    wceq
    @40
    @13
    cJ
    toponuni
    syl
    #
    sseqtrd
    wph
    @28
    @6
    limcres.i
    adantr
    @11
    @13
    cc
    @18
    wf
    @29
    @11
    vz
    @13
    @17
    cc
    @18
    @14
    @13
    wcel
    @11
    @14
    cA
    wcel
    #
    @14
    @12
    wcel
    #
    wo
    @17
    cc
    wcel
    #
    @14
    cA
    @12
    elun
    @11
    @46
    @48
    @47
    @11
    @46
    wa
    @15
    @4
    @16
    cc
    wph
    @3
    @5
    @46
    simplrr
    @11
    cA
    cc
    @14
    cF
    wph
    cA
    cc
    cF
    wf
    @6
    limcres.f
    adantr
    #
    ffvelrnda
    ifcld
    @11
    @47
    wa
    #
    @17
    @4
    cc
    @50
    @15
    @4
    @16
    @47
    @15
    @11
    @14
    cB
    elsni
    adantl
    iftrued
    wph
    @3
    @5
    @47
    simplrr
    eqeltrd
    jaodan
    sylan2b
    @18
    eqid
    #
    fmptd
    @11
    @13
    @27
    cc
    @18
    @45
    feq2d
    mpbid
    @20
    cB
    @18
    cJ
    cK
    @27
    cc
    @27
    eqid
    cc
    cK
    @36
    toponunii
    cnprest
    syl22anc
    @11
    vz
    cA
    cB
    @4
    cF
    @18
    cJ
    cK
    limcres.j
    limcres.k
    @51
    @49
    @37
    @38
    ellimc
    @11
    @7
    vz
    @20
    @15
    @4
    @14
    @0
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cK
    @20
    crest
    co
    #
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    @25
    @11
    vz
    cC
    cB
    @4
    @0
    @54
    @55
    cK
    @55
    eqid
    limcres.k
    @54
    eqid
    @11
    cA
    cc
    cC
    cF
    @49
    @43
    fssresd
    @11
    cC
    cA
    cc
    @43
    @37
    sstrd
    @38
    ellimc
    @11
    @54
    @21
    @57
    @24
    @11
    @21
    vz
    @20
    @17
    cmpt
    @54
    @11
    vz
    @13
    @20
    @17
    @44
    resmptd
    vz
    @20
    @53
    @17
    @14
    @20
    wcel
    #
    @14
    cC
    wcel
    #
    @15
    wo
    #
    @53
    @17
    wceq
    @58
    @59
    @47
    wo
    @60
    @14
    cC
    @12
    elun
    @47
    @15
    @59
    vz
    cB
    velsn
    orbi2i
    bitri
    @60
    @15
    @52
    @16
    @4
    @60
    @15
    wn
    #
    wa
    @59
    @61
    wa
    @52
    @16
    wceq
    #
    @59
    @15
    pm5.61
    @59
    @62
    @61
    @14
    cC
    cF
    fvres
    adantr
    sylbi
    ifeq2da
    sylbi
    mpteq2ia
    syl6reqr
    @11
    cB
    @56
    @23
    @11
    @55
    @22
    cK
    ccnp
    @11
    @22
    @32
    @20
    crest
    co
    #
    @55
    cJ
    @32
    @20
    crest
    limcres.j
    oveq1i
    @11
    @34
    @42
    @13
    cvv
    wcel
    #
    @63
    @55
    wceq
    @34
    @11
    @36
    a1i
    @44
    @11
    @35
    @64
    @39
    @13
    cc
    cnex
    ssex
    syl
    @20
    @13
    cK
    @33
    cvv
    restabs
    syl3anc
    syl5req
    oveq1d
    fveq1d
    eleq12d
    bitrd
    3bitr4rd
    ex
    pm5.21ndd
    eqrdv
end
