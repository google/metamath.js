include "coms.mm"
include "cfv.mm"
include "cle.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "cpw.mm"
include "crab.mm"
include "cesum.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "cinf.mm"
include "cres.mm"
include "wceq.mm"
include "wcel.mm"
include "wi.mm"
include "adantr.mm"
include "sstr2.mm"
include "syl.mm"
include "anim1d.mm"
include "ss2rabdv.mm"
include "resmpt.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "rnss.mm"
include "wral.mm"
include "wf.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "simplr.mm"
include "sseldi.mm"
include "elpwi.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "simpr.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "vex.mm"
include "nfcv.mm"
include "esumcl.mm"
include "mpan.mm"
include "eqid.mm"
include "rnmptss.mm"
include "xrge0infssd.mm"
include "sstrd.mm"
include "omsfval.mm"
include "syl3anc.mm"
include "3brtr4d.mm"
include "fveq1i.mm"
include "3brtr4g.mm"

theorem omsmon
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  assume oms.m: |- M = ( toOMeas ` R )
  assume oms.o: |- ( ph -> Q e. V )
  assume oms.r: |- ( ph -> R : Q --> ( 0 [,] +oo ) )
  assume omsmon.a: |- ( ph -> A C_ B )
  assume omsmon.b: |- ( ph -> B C_ U. Q )


  assert |- ( ph -> ( M ` A ) <_ ( M ` B ) )

  proof
    wph
    cA
    cR
    coms
    cfv
    #
    cfv
    #
    cB
    @0
    cfv
    #
    cA
    cM
    cfv
    cB
    cM
    cfv
    cle
    wph
    vx
    cA
    vz
    cv
    #
    cuni
    #
    wss
    #
    @3
    com
    cdom
    wbr
    #
    wa
    #
    vz
    cR
    cdm
    #
    cpw
    #
    crab
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cfv
    #
    vy
    cesum
    #
    cmpt
    #
    crn
    #
    cc0
    cpnf
    cicc
    co
    #
    clt
    cinf
    #
    vx
    cB
    @4
    wss
    #
    @6
    wa
    #
    vz
    @9
    crab
    #
    @14
    cmpt
    #
    crn
    #
    @17
    clt
    cinf
    #
    @1
    @2
    cle
    wph
    @16
    @23
    wph
    @22
    @15
    wss
    @23
    @16
    wss
    wph
    @22
    @15
    @21
    cres
    #
    @15
    wph
    @21
    @10
    wss
    @25
    @22
    wceq
    wph
    @20
    @7
    vz
    @9
    wph
    @3
    @9
    wcel
    #
    wa
    #
    @19
    @5
    @6
    @27
    cA
    cB
    wss
    #
    @19
    @5
    wi
    wph
    @28
    @26
    omsmon.a
    adantr
    cA
    cB
    @4
    sstr2
    syl
    anim1d
    ss2rabdv
    vx
    @10
    @21
    @14
    resmpt
    syl
    @15
    @21
    resss
    syl6eqssr
    @22
    @15
    rnss
    syl
    wph
    @14
    @17
    wcel
    #
    vx
    @10
    wral
    @16
    @17
    wss
    wph
    @29
    vx
    @10
    wph
    @11
    @10
    wcel
    #
    wa
    #
    @13
    @17
    wcel
    #
    vy
    @11
    wral
    #
    @29
    @31
    @32
    vy
    @11
    @31
    @12
    @11
    wcel
    #
    wa
    #
    cQ
    @17
    @12
    cR
    wph
    cQ
    @17
    cR
    wf
    #
    @30
    @34
    oms.r
    ad2antrr
    @35
    @11
    cQ
    @12
    @35
    @11
    @8
    cQ
    @35
    @11
    @9
    wcel
    @11
    @8
    wss
    @35
    @10
    @9
    @11
    @7
    vz
    @9
    ssrab2
    wph
    @30
    @34
    simplr
    sseldi
    @11
    @8
    elpwi
    syl
    wph
    @8
    cQ
    wceq
    #
    @30
    @34
    wph
    @36
    @37
    oms.r
    cQ
    @17
    cR
    fdm
    syl
    ad2antrr
    sseqtrd
    @31
    @34
    simpr
    sseldd
    ffvelrnd
    ralrimiva
    @11
    cvv
    wcel
    @33
    @29
    vx
    vex
    @11
    @13
    vy
    cvv
    vy
    @11
    nfcv
    esumcl
    mpan
    syl
    ralrimiva
    vx
    @10
    @14
    @17
    @15
    @15
    eqid
    rnmptss
    syl
    xrge0infssd
    wph
    cQ
    cV
    wcel
    #
    @36
    cA
    cQ
    cuni
    #
    wss
    @1
    @18
    wceq
    oms.o
    oms.r
    wph
    cA
    cB
    @39
    omsmon.a
    omsmon.b
    sstrd
    vx
    vy
    vz
    cA
    cQ
    cR
    cV
    omsfval
    syl3anc
    wph
    @38
    @36
    cB
    @39
    wss
    @2
    @24
    wceq
    oms.o
    oms.r
    omsmon.b
    vx
    vy
    vz
    cB
    cQ
    cR
    cV
    omsfval
    syl3anc
    3brtr4d
    cA
    cM
    @0
    oms.m
    fveq1i
    cB
    cM
    @0
    oms.m
    fveq1i
    3brtr4g
end
