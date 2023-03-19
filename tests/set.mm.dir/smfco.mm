include "ccnv.mm"
include "cdm.mm"
include "cima.mm"
include "ccom.mm"
include "nfv.mm"
include "cuni.mm"
include "wss.mm"
include "cnvimass.mm"
include "a1i.mm"
include "eqid.mm"
include "smfdmss.mm"
include "sstrd.mm"
include "crn.mm"
include "cr.mm"
include "ctop.mm"
include "wcel.mm"
include "cioo.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "salgencld.mm"
include "smff.mm"
include "ffund.mm"
include "fco3.mm"
include "frnd.mm"
include "fssd.mm"
include "cv.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cmnf.mm"
include "co.mm"
include "crest.mm"
include "wf.mm"
include "adantr.mm"
include "cxr.mm"
include "rexr.mm"
include "adantl.mm"
include "preimaioomnf.mm"
include "eqcomd.mm"
include "wceq.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "3eqtrd.mm"
include "cin.mm"
include "wrex.mm"
include "csalg.mm"
include "csmblfn.mm"
include "simpr.mm"
include "smfpreimalt.mm"
include "eqeltrd.mm"
include "wb.mm"
include "cvv.mm"
include "elexd.mm"
include "dmexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "imaeq2.mm"
include "3ad2ant3.mm"
include "ovexd.mm"
include "cnvexg.mm"
include "syl.mm"
include "imaexg.mm"
include "smfpimbor1.mm"
include "elrestd.mm"
include "wfun.mm"
include "inpreima.mm"
include "restabs.mm"
include "syl3anc.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "3adant3.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "issmfd.mm"

theorem smfco
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cF: class F
  let cH: class H
  let cJ: class J
  let ve: setvar e
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume smfco.s: |- ( ph -> S e. SAlg )
  assume smfco.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfco.j: |- J = ( topGen ` ran (,) )
  assume smfco.b: |- B = ( SalGen ` J )
  assume smfco.h: |- ( ph -> H e. ( SMblFn ` B ) )


  assert |- ( ph -> ( H o. F ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cF
    ccnv
    #
    cH
    cdm
    #
    cima
    #
    cS
    cH
    cF
    ccom
    #
    va
    wph
    va
    nfv
    smfco.s
    wph
    @2
    cF
    cdm
    #
    cS
    cuni
    @2
    @4
    wss
    #
    wph
    cF
    @1
    cnvimass
    a1i
    #
    wph
    @4
    cS
    cF
    smfco.s
    smfco.f
    @4
    eqid
    #
    smfdmss
    sstrd
    wph
    @2
    cH
    crn
    cr
    @3
    wph
    cH
    cF
    wph
    @1
    cr
    cH
    wph
    @1
    cB
    cH
    wph
    cB
    ctop
    cJ
    cJ
    ctop
    wcel
    wph
    cJ
    cioo
    crn
    ctg
    cfv
    ctop
    smfco.j
    retop
    eqeltri
    a1i
    smfco.b
    salgencld
    #
    smfco.h
    @1
    eqid
    #
    smff
    #
    ffund
    wph
    @4
    cr
    cF
    wph
    @4
    cS
    cF
    smfco.s
    smfco.f
    @7
    smff
    ffund
    #
    fco3
    wph
    @1
    cr
    cH
    @10
    frnd
    fssd
    #
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    vx
    cv
    #
    @3
    cfv
    @13
    clt
    wbr
    vx
    @2
    crab
    #
    @0
    cH
    ccnv
    #
    cmnf
    @13
    cioo
    co
    #
    cima
    #
    cima
    #
    cS
    @2
    crest
    co
    #
    @15
    @17
    @3
    ccnv
    #
    @19
    cima
    #
    @0
    @18
    ccom
    #
    @19
    cima
    #
    @21
    @15
    @24
    @17
    @15
    vx
    @2
    @13
    @3
    wph
    @2
    cr
    @3
    wf
    @14
    @12
    adantr
    @14
    @13
    cxr
    wcel
    wph
    @13
    rexr
    adantl
    #
    preimaioomnf
    eqcomd
    @24
    @26
    wceq
    @15
    @23
    @25
    @19
    cH
    cF
    cnvco
    imaeq1i
    a1i
    @26
    @21
    wceq
    @15
    @0
    @18
    @19
    imaco
    a1i
    3eqtrd
    @15
    @20
    ve
    cv
    #
    @1
    cin
    #
    wceq
    #
    ve
    cB
    wrex
    #
    @21
    @22
    wcel
    #
    @15
    @20
    cB
    @1
    crest
    co
    #
    wcel
    #
    @31
    @15
    @20
    @16
    cH
    cfv
    @13
    clt
    wbr
    vx
    @1
    crab
    #
    @33
    @15
    @35
    @20
    @15
    @20
    @35
    @15
    vx
    @1
    @13
    cH
    wph
    @1
    cr
    cH
    wf
    @14
    @10
    adantr
    @27
    preimaioomnf
    eqcomd
    eqcomd
    @15
    vx
    @13
    @1
    cB
    cH
    wph
    cB
    csalg
    wcel
    @14
    @8
    adantr
    wph
    cH
    cB
    csmblfn
    cfv
    #
    wcel
    @14
    smfco.h
    adantr
    @9
    wph
    @14
    simpr
    smfpreimalt
    eqeltrd
    wph
    @34
    @31
    wb
    #
    @14
    wph
    cB
    cvv
    wcel
    @1
    cvv
    wcel
    @37
    wph
    cB
    csalg
    @8
    elexd
    wph
    cH
    @36
    smfco.h
    dmexd
    ve
    @20
    @1
    cB
    cvv
    cvv
    elrest
    syl2anc
    adantr
    mpbid
    @15
    @30
    @32
    ve
    cB
    wph
    @28
    cB
    wcel
    #
    @30
    @32
    wi
    wi
    @14
    wph
    @38
    @30
    @32
    wph
    @38
    @30
    w3a
    @21
    @0
    @29
    cima
    #
    @22
    @30
    wph
    @21
    @39
    wceq
    @38
    @20
    @29
    @0
    imaeq2
    3ad2ant3
    wph
    @38
    @39
    @22
    wcel
    #
    @30
    wph
    @38
    wa
    #
    @40
    @0
    @28
    cima
    #
    @2
    cin
    #
    cS
    @4
    crest
    co
    #
    @2
    crest
    co
    #
    wcel
    @41
    @43
    @2
    @44
    cvv
    cvv
    @42
    @41
    cS
    @4
    crest
    ovexd
    wph
    @2
    cvv
    wcel
    #
    @38
    wph
    @0
    cvv
    wcel
    #
    @46
    wph
    cF
    cvv
    wcel
    @47
    wph
    cF
    cS
    csmblfn
    cfv
    #
    smfco.f
    elexd
    cF
    cvv
    cnvexg
    syl
    @0
    @1
    cvv
    imaexg
    syl
    adantr
    @41
    cB
    @4
    @42
    cS
    @28
    cF
    cJ
    wph
    cS
    csalg
    wcel
    #
    @38
    smfco.s
    adantr
    wph
    cF
    @48
    wcel
    @38
    smfco.f
    adantr
    @7
    smfco.j
    smfco.b
    wph
    @38
    simpr
    @42
    eqid
    smfpimbor1
    @43
    eqid
    elrestd
    @41
    @39
    @43
    @22
    @45
    wph
    @39
    @43
    wceq
    #
    @38
    wph
    cF
    wfun
    @50
    @11
    @28
    @1
    cF
    inpreima
    syl
    adantr
    wph
    @22
    @45
    wceq
    @38
    wph
    @45
    @22
    wph
    @49
    @5
    @4
    cvv
    wcel
    @45
    @22
    wceq
    smfco.s
    @6
    wph
    cF
    @48
    smfco.f
    dmexd
    @2
    @4
    cS
    csalg
    cvv
    restabs
    syl3anc
    eqcomd
    adantr
    eleq12d
    mpbird
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimdv
    mpd
    eqeltrd
    issmfd
end
