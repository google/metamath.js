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
include "cuni.mm"
include "wfo.mm"
include "wb.mm"
include "ctop.mm"
include "cntop1.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wfn.mm"
include "wf.mm"
include "cnf2.mm"
include "ffn.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "elqtop3.mm"
include "syl2anc.mm"
include "foimacnv.mm"
include "sylan.mm"
include "adantrr.mm"
include "wral.mm"
include "simprr.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem qtopomap
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
  assume qtopomap.7: |- ( ( ph /\ x e. J ) -> ( F " x ) e. K )

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
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @11
    cY
    cF
    wfo
    #
    @5
    @9
    wb
    wph
    cJ
    ctop
    wcel
    #
    @12
    wph
    @1
    @14
    qtopomap.5
    cF
    cJ
    cK
    cntop1
    syl
    cJ
    @11
    @11
    eqid
    toptopon
    sylib
    #
    wph
    cF
    @11
    wfn
    #
    @3
    @13
    wph
    @11
    cY
    cF
    wf
    #
    @16
    wph
    @12
    @2
    @1
    @17
    @15
    qtopomap.4
    qtopomap.5
    cF
    cJ
    cK
    @11
    cY
    cnf2
    syl3anc
    @11
    cY
    cF
    ffn
    syl
    qtopomap.6
    @11
    cY
    cF
    df-fo
    sylanbrc
    #
    @4
    cF
    cJ
    @11
    cY
    elqtop3
    syl2anc
    wph
    @9
    @10
    wph
    @9
    wa
    #
    cF
    @7
    cima
    #
    @4
    cK
    wph
    @6
    @20
    @4
    wceq
    #
    @8
    wph
    @13
    @6
    @21
    @18
    @11
    cY
    @4
    cF
    foimacnv
    sylan
    adantrr
    @19
    @8
    cF
    vx
    cv
    #
    cima
    #
    cK
    wcel
    #
    vx
    cJ
    wral
    #
    @20
    cK
    wcel
    #
    wph
    @6
    @8
    simprr
    wph
    @25
    @9
    wph
    @24
    vx
    cJ
    qtopomap.7
    ralrimiva
    adantr
    @24
    @26
    vx
    @7
    cJ
    @22
    @7
    wceq
    @23
    @20
    cK
    @22
    @7
    cF
    imaeq2
    eleq1d
    rspcv
    sylc
    eqeltrrd
    ex
    sylbid
    ssrdv
    eqssd
end
