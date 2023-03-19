include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "w3a.mm"
include "evth.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "wf.mm"
include "ccn.mm"
include "co.mm"
include "eqid.mm"
include "fcnre.mm"
include "frn.mm"
include "syl.mm"
include "adantr.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "simpr.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "wex.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "3syl.mm"
include "biimpa.mm"
include "df-rex.mm"
include "sylib.mm"
include "adantlr.mm"
include "simprr.mm"
include "simpllr.mm"
include "simprl.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspccva.mm"
include "eqbrtrrd.mm"
include "exlimddv.mm"
include "ralrimiva.mm"
include "adantrl.mm"
include "ubelsupr.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "sseldd.mm"
include "simplrr.mm"
include "sylancom.mm"
include "breqtrrd.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "3jca.mm"
include "rexlimddv.mm"

theorem cncmpmax
  let wph: wff ph
  let vt: setvar t
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume cncmpmax.1: |- T = U. J
  assume cncmpmax.2: |- K = ( topGen ` ran (,) )
  assume cncmpmax.3: |- ( ph -> J e. Comp )
  assume cncmpmax.4: |- ( ph -> F e. ( J Cn K ) )
  assume cncmpmax.5: |- ( ph -> T =/= (/) )

  disjoint F t
  disjoint T t
  disjoint ph t
  disjoint J t
  disjoint K t
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint T s
  disjoint T x
  disjoint T y
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint J x
  assert |- ( ph -> ( sup ( ran F , RR , < ) e. ran F /\ sup ( ran F , RR , < ) e. RR /\ A. t e. T ( F ` t ) <_ sup ( ran F , RR , < ) ) )

  proof
    wph
    vt
    cv
    #
    cF
    cfv
    #
    vx
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
    #
    cF
    crn
    #
    cr
    clt
    csup
    #
    @6
    wcel
    #
    @7
    cr
    wcel
    #
    @1
    @7
    cle
    wbr
    #
    vt
    cT
    wral
    #
    w3a
    vx
    cT
    wph
    vx
    vt
    cF
    cJ
    cK
    cT
    cncmpmax.1
    cncmpmax.2
    cncmpmax.3
    cncmpmax.4
    cncmpmax.5
    evth
    wph
    @2
    cT
    wcel
    #
    @5
    wa
    #
    wa
    #
    @8
    @9
    @11
    @14
    @7
    @3
    @6
    @14
    @3
    @7
    @14
    @6
    cr
    wss
    #
    @3
    @6
    wcel
    #
    vy
    cv
    #
    @3
    cle
    wbr
    #
    vy
    @6
    wral
    #
    @3
    @7
    wceq
    wph
    @15
    @13
    wph
    cT
    cr
    cF
    wf
    #
    @15
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
    cncmpmax.2
    cncmpmax.1
    @21
    eqid
    cncmpmax.4
    fcnre
    #
    cT
    cr
    cF
    frn
    syl
    adantr
    #
    wph
    @12
    @16
    @5
    wph
    @12
    wa
    #
    cF
    wfun
    #
    @2
    cF
    cdm
    #
    wcel
    @16
    wph
    @25
    @12
    wph
    @20
    @25
    @22
    cT
    cr
    cF
    ffun
    syl
    adantr
    @24
    @2
    cT
    @26
    wph
    @12
    simpr
    @24
    @20
    @26
    cT
    wceq
    wph
    @20
    @12
    @22
    adantr
    cT
    cr
    cF
    fdm
    syl
    eleqtrrd
    @2
    cF
    fvelrn
    syl2anc
    adantrr
    #
    wph
    @5
    @19
    @12
    wph
    @5
    wa
    #
    @18
    vy
    @6
    @28
    @17
    @6
    wcel
    #
    wa
    #
    vs
    cv
    #
    cT
    wcel
    #
    @31
    cF
    cfv
    #
    @17
    wceq
    #
    wa
    #
    @18
    vs
    wph
    @29
    @35
    vs
    wex
    #
    @5
    wph
    @29
    wa
    @34
    vs
    cT
    wrex
    #
    @36
    wph
    @29
    @37
    wph
    @20
    cF
    cT
    wfn
    @29
    @37
    wb
    @22
    cT
    cr
    cF
    ffn
    vs
    cT
    @17
    cF
    fvelrnb
    3syl
    biimpa
    @34
    vs
    cT
    df-rex
    sylib
    adantlr
    @30
    @35
    wa
    #
    @33
    @17
    @3
    cle
    @30
    @32
    @34
    simprr
    @38
    @5
    @32
    @33
    @3
    cle
    wbr
    #
    wph
    @5
    @29
    @35
    simpllr
    @30
    @32
    @34
    simprl
    @4
    @39
    vt
    @31
    cT
    @0
    @31
    wceq
    #
    @1
    @33
    @3
    cle
    @0
    @31
    cF
    fveq2
    #
    breq1d
    rspccva
    #
    syl2anc
    eqbrtrrd
    exlimddv
    ralrimiva
    adantrl
    vy
    @6
    @3
    ubelsupr
    syl3anc
    eqcomd
    #
    @27
    eqeltrd
    #
    @14
    @6
    cr
    @7
    @23
    @44
    sseldd
    @14
    @33
    @7
    cle
    wbr
    #
    vs
    cT
    wral
    @11
    @14
    @45
    vs
    cT
    @14
    @32
    wa
    @33
    @3
    @7
    cle
    @14
    @32
    @5
    @39
    wph
    @12
    @5
    @32
    simplrr
    @42
    sylancom
    @14
    @7
    @3
    wceq
    @32
    @43
    adantr
    breqtrrd
    ralrimiva
    @10
    @45
    vt
    vs
    cT
    @40
    @1
    @33
    @7
    cle
    @41
    breq1d
    cbvralv
    sylibr
    3jca
    rexlimddv
end
