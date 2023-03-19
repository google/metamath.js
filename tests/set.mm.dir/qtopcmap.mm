include "cqtop.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "crn.mm"
include "wceq.mm"
include "wss.mm"
include "qtopss.mm"
include "syl3anc.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wa.mm"
include "ctop.mm"
include "cuni.mm"
include "wfo.mm"
include "wb.mm"
include "cntop1.mm"
include "syl.mm"
include "wfn.mm"
include "wf.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "ffn.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "elqtop2.mm"
include "syl2anc.mm"
include "cdif.mm"
include "ccld.mm"
include "adantr.mm"
include "difss.mm"
include "foimacnv.mm"
include "sylancl.mm"
include "toponuni.mm"
include "difeq1d.mm"
include "eqtrd.mm"
include "wral.mm"
include "wfun.mm"
include "fofun.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "4syl.mm"
include "fimacnv.mm"
include "simprr.mm"
include "opncld.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "topontop.mm"
include "simprl.mm"
include "sseqtrd.mm"
include "isopn2.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem qtopcmap
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cK: class K
  let cY: class Y
  let vy: setvar y
  assume qtopomap.4: |- ( ph -> K e. ( TopOn ` Y ) )
  assume qtopomap.5: |- ( ph -> F e. ( J Cn K ) )
  assume qtopomap.6: |- ( ph -> ran F = Y )
  assume qtopcmap.7: |- ( ( ph /\ x e. ( Clsd ` J ) ) -> ( F " x ) e. ( Clsd ` K ) )

  disjoint F x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint Y x
  disjoint x y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint ph y
  assert |- ( ph -> K = ( J qTop F ) )

  proof
    wph
    cK
    cJ
    cF
    cqtop
    co
    #
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cF
    crn
    cY
    wceq
    #
    cK
    @0
    wss
    qtopomap.5
    qtopomap.4
    qtopomap.6
    cF
    cJ
    cK
    cY
    qtopss
    syl3anc
    wph
    vy
    @0
    cK
    wph
    vy
    cv
    #
    @0
    wcel
    #
    @4
    cY
    wss
    #
    cF
    ccnv
    #
    @4
    cima
    #
    cJ
    wcel
    #
    wa
    #
    @4
    cK
    wcel
    #
    wph
    cJ
    ctop
    wcel
    #
    cJ
    cuni
    #
    cY
    cF
    wfo
    #
    @5
    @10
    wb
    wph
    @1
    @12
    qtopomap.5
    cF
    cJ
    cK
    cntop1
    syl
    #
    wph
    cF
    @13
    wfn
    #
    @3
    @14
    wph
    @13
    cY
    cF
    wf
    #
    @16
    wph
    cJ
    @13
    ctopon
    cfv
    wcel
    #
    @2
    @1
    @17
    wph
    @12
    @18
    @15
    cJ
    @13
    @13
    eqid
    #
    toptopon
    sylib
    qtopomap.4
    qtopomap.5
    cF
    cJ
    cK
    @13
    cY
    cnf2
    syl3anc
    #
    @13
    cY
    cF
    ffn
    syl
    qtopomap.6
    @13
    cY
    cF
    df-fo
    sylanbrc
    #
    @4
    cF
    cJ
    ctop
    @13
    cY
    @19
    elqtop2
    syl2anc
    wph
    @10
    @11
    wph
    @10
    wa
    #
    @11
    cK
    cuni
    #
    @4
    cdif
    #
    cK
    ccld
    cfv
    #
    wcel
    #
    @22
    cF
    @7
    cY
    @4
    cdif
    #
    cima
    #
    cima
    #
    @24
    @25
    @22
    @29
    @27
    @24
    @22
    @14
    @27
    cY
    wss
    @29
    @27
    wceq
    wph
    @14
    @10
    @21
    adantr
    #
    cY
    @4
    difss
    @13
    cY
    @27
    cF
    foimacnv
    sylancl
    @22
    cY
    @23
    @4
    @22
    @2
    cY
    @23
    wceq
    wph
    @2
    @10
    qtopomap.4
    adantr
    #
    cY
    cK
    toponuni
    syl
    #
    difeq1d
    eqtrd
    @22
    @28
    cJ
    ccld
    cfv
    #
    wcel
    cF
    vx
    cv
    #
    cima
    #
    @25
    wcel
    #
    vx
    @33
    wral
    #
    @29
    @25
    wcel
    #
    @22
    @28
    @13
    @8
    cdif
    #
    @33
    @22
    @28
    @7
    cY
    cima
    #
    @8
    cdif
    #
    @39
    @22
    @14
    cF
    wfun
    @7
    ccnv
    wfun
    @28
    @41
    wceq
    @30
    @13
    cY
    cF
    fofun
    cF
    funcnvcnv
    cY
    @4
    @7
    imadif
    4syl
    @22
    @40
    @13
    @8
    @22
    @17
    @40
    @13
    wceq
    wph
    @17
    @10
    @20
    adantr
    @13
    cY
    cF
    fimacnv
    syl
    difeq1d
    eqtrd
    @22
    @12
    @9
    @39
    @33
    wcel
    wph
    @12
    @10
    @15
    adantr
    wph
    @6
    @9
    simprr
    @8
    cJ
    @13
    @19
    opncld
    syl2anc
    eqeltrd
    wph
    @37
    @10
    wph
    @36
    vx
    @33
    qtopcmap.7
    ralrimiva
    adantr
    @36
    @38
    vx
    @28
    @33
    @34
    @28
    wceq
    @35
    @29
    @25
    @34
    @28
    cF
    imaeq2
    eleq1d
    rspcv
    sylc
    eqeltrrd
    @22
    cK
    ctop
    wcel
    #
    @4
    @23
    wss
    @11
    @26
    wb
    @22
    @2
    @42
    @31
    cY
    cK
    topontop
    syl
    @22
    @4
    cY
    @23
    wph
    @6
    @9
    simprl
    @32
    sseqtrd
    @4
    cK
    @23
    @23
    eqid
    isopn2
    syl2anc
    mpbird
    ex
    sylbid
    ssrdv
    eqssd
end
