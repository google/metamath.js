include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wss.mm"
include "wrex.mm"
include "wfn.mm"
include "wf.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "eqid.mm"
include "fcnre.mm"
include "df-f.mm"
include "sylib.mm"
include "simprd.mm"
include "wfun.mm"
include "cdm.mm"
include "simpld.mm"
include "fnfun.mm"
include "syl.mm"
include "adantr.mm"
include "wceq.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq2.mm"
include "breq1.mm"
include "ralbid.mm"
include "rspcev.mm"
include "sylan.mm"
include "evth2f.mm"
include "r19.29a.mm"
include "nfv.mm"
include "simpr.mm"
include "wb.mm"
include "ad2antrr.mm"
include "fvelrnbf.mm"
include "mpbid.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfrn.mm"
include "nfcri.mm"
include "wi.mm"
include "rspa.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "ex.mm"
include "ad2antlr.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimi.mm"
include "reximdv.mm"
include "lbinfcl.mm"
include "sseldd.mm"
include "dffn3.mm"
include "ffvelrnda.mm"
include "lbinfle.mm"
include "syl3anc.mm"
include "3jca.mm"

theorem stoweidlem29
  let wph: wff ph
  let vt: setvar t
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume stoweidlem29.1: |- F/_ t F
  assume stoweidlem29.2: |- F/ t ph
  assume stoweidlem29.3: |- T = U. J
  assume stoweidlem29.4: |- K = ( topGen ` ran (,) )
  assume stoweidlem29.5: |- ( ph -> J e. Comp )
  assume stoweidlem29.6: |- ( ph -> F e. ( J Cn K ) )
  assume stoweidlem29.7: |- ( ph -> T =/= (/) )

  disjoint T t
  disjoint J t
  disjoint K t
  disjoint s t
  disjoint s x
  disjoint T s
  disjoint t x
  disjoint T x
  disjoint F s
  disjoint F x
  disjoint J s
  disjoint ph s
  disjoint ph x
  disjoint t y
  disjoint x y
  disjoint T y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( inf ( ran F , RR , < ) e. ran F /\ inf ( ran F , RR , < ) e. RR /\ A. t e. T inf ( ran F , RR , < ) <_ ( F ` t ) ) )

  proof
    wph
    cF
    crn
    #
    cr
    clt
    cinf
    #
    @0
    wcel
    #
    @1
    cr
    wcel
    @1
    vt
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vt
    cT
    wral
    wph
    @0
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @0
    wral
    #
    vx
    @0
    wrex
    #
    @2
    wph
    cF
    cT
    wfn
    #
    @6
    wph
    cT
    cr
    cF
    wf
    #
    @12
    @6
    wa
    wph
    cJ
    cK
    ccn
    co
    #
    cT
    cF
    cJ
    cK
    stoweidlem29.4
    stoweidlem29.3
    @14
    eqid
    stoweidlem29.6
    fcnre
    #
    cT
    cr
    cF
    df-f
    sylib
    #
    simprd
    #
    wph
    @7
    @4
    cle
    wbr
    #
    vt
    cT
    wral
    #
    vx
    @0
    wrex
    #
    @11
    wph
    vs
    cv
    #
    cF
    cfv
    #
    @4
    cle
    wbr
    #
    vt
    cT
    wral
    #
    @20
    vs
    cT
    wph
    @21
    cT
    wcel
    #
    wa
    #
    @22
    @0
    wcel
    #
    @24
    @20
    @26
    cF
    wfun
    #
    @21
    cF
    cdm
    #
    wcel
    #
    @27
    wph
    @28
    @25
    wph
    @12
    @28
    wph
    @12
    @6
    @16
    simpld
    #
    cT
    cF
    fnfun
    syl
    adantr
    wph
    @25
    @30
    wph
    cT
    @29
    @21
    wph
    @29
    cT
    wph
    @13
    @29
    cT
    wceq
    @15
    cT
    cr
    cF
    fdm
    syl
    eqcomd
    eleq2d
    biimpa
    @21
    cF
    fvelrn
    syl2anc
    @19
    @24
    vx
    @22
    @0
    @7
    @22
    wceq
    @18
    @23
    vt
    cT
    vt
    @7
    @22
    vt
    @21
    cF
    stoweidlem29.1
    vt
    @21
    nfcv
    nffv
    nfeq2
    @7
    @22
    @4
    cle
    breq1
    ralbid
    rspcev
    sylan
    wph
    vs
    vt
    cF
    cJ
    cK
    cT
    vs
    cF
    nfcv
    stoweidlem29.1
    vs
    cT
    nfcv
    vt
    cT
    nfcv
    #
    stoweidlem29.3
    stoweidlem29.4
    stoweidlem29.5
    stoweidlem29.6
    stoweidlem29.7
    evth2f
    r19.29a
    wph
    @19
    @10
    vx
    @0
    wph
    @19
    @10
    wph
    @19
    wa
    #
    @9
    vy
    @0
    @33
    vy
    nfv
    @33
    @8
    @0
    wcel
    #
    @9
    @33
    @34
    wa
    #
    @4
    @8
    wceq
    #
    vt
    cT
    wrex
    #
    @9
    @35
    @34
    @37
    @33
    @34
    simpr
    @35
    @12
    @34
    @37
    wb
    wph
    @12
    @19
    @34
    @31
    ad2antrr
    vt
    cT
    @8
    cF
    @32
    vt
    @8
    nfcv
    stoweidlem29.1
    fvelrnbf
    syl
    mpbid
    @35
    @36
    @9
    vt
    cT
    @33
    @34
    vt
    wph
    @19
    vt
    stoweidlem29.2
    @18
    vt
    cT
    nfra1
    nfan
    vt
    vy
    @0
    vt
    cF
    stoweidlem29.1
    nfrn
    nfcri
    nfan
    @9
    vt
    nfv
    @19
    @3
    cT
    wcel
    #
    @36
    @9
    wi
    #
    wi
    wph
    @34
    @19
    @38
    @39
    @19
    @38
    wa
    @18
    @36
    @9
    @18
    vt
    cT
    rspa
    @4
    @8
    @7
    cle
    breq2
    syl5ibcom
    ex
    ad2antlr
    rexlimd
    mpd
    ex
    ralrimi
    ex
    reximdv
    mpd
    #
    vx
    vy
    @0
    lbinfcl
    syl2anc
    #
    wph
    @0
    cr
    @1
    @17
    @41
    sseldd
    wph
    @5
    vt
    cT
    stoweidlem29.2
    wph
    @38
    @5
    wph
    @38
    wa
    @6
    @11
    @4
    @0
    wcel
    @5
    wph
    @6
    @38
    @17
    adantr
    wph
    @11
    @38
    @40
    adantr
    wph
    cT
    @0
    @3
    cF
    wph
    @12
    cT
    @0
    cF
    wf
    @31
    cT
    cF
    dffn3
    sylib
    ffvelrnda
    vx
    vy
    @4
    @0
    lbinfle
    syl3anc
    ex
    ralrimi
    3jca
end
