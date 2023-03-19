include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "ccld.mm"
include "wral.mm"
include "cnf2.mm"
include "3expa.mm"
include "cnclima.mm"
include "ralrimiva.mm"
include "adantl.mm"
include "jca.mm"
include "simprl.mm"
include "cuni.mm"
include "cdif.mm"
include "wceq.mm"
include "toponuni.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "fimacnv.mm"
include "eqcomd.mm"
include "syl.mm"
include "eqtr3d.mm"
include "difeq1d.mm"
include "wfun.mm"
include "ffun.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "4syl.mm"
include "eqtr4d.mm"
include "ad3antlr.mm"
include "ctop.mm"
include "topontop.mm"
include "eqid.mm"
include "opncld.mm"
include "sylancom.mm"
include "eqeltrd.mm"
include "simplrr.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "wss.mm"
include "wb.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sseqtrd.mm"
include "isopn2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "iscn.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem iscncl
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x

  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X y
  disjoint Y y
  disjoint F x
  disjoint x y
  disjoint J x
  disjoint K x
  disjoint X x
  disjoint Y x
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. y e. ( Clsd ` K ) ( `' F " y ) e. ( Clsd ` J ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cJ
    ccld
    cfv
    #
    wcel
    #
    vy
    cK
    ccld
    cfv
    #
    wral
    #
    wa
    #
    @2
    @3
    wa
    @4
    @11
    @0
    @1
    @3
    @4
    cF
    cJ
    cK
    cX
    cY
    cnf2
    3expa
    @3
    @11
    @2
    @3
    @9
    vy
    @10
    @6
    cF
    cJ
    cK
    cnclima
    ralrimiva
    adantl
    jca
    @2
    @12
    wa
    #
    @3
    @4
    @5
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    #
    @2
    @4
    @11
    simprl
    @13
    @16
    vx
    cK
    @13
    @14
    cK
    wcel
    #
    wa
    #
    @16
    cJ
    cuni
    #
    @15
    cdif
    #
    @8
    wcel
    #
    @19
    @21
    @5
    cY
    @14
    cdif
    #
    cima
    #
    @8
    @19
    @21
    @5
    cY
    cima
    #
    @15
    cdif
    #
    @24
    @19
    @20
    @25
    @15
    @19
    cX
    @20
    @25
    @0
    cX
    @20
    wceq
    @1
    @12
    @18
    cX
    cJ
    toponuni
    ad3antrrr
    #
    @19
    @4
    cX
    @25
    wceq
    @2
    @4
    @11
    @18
    simplrl
    #
    @4
    @25
    cX
    cX
    cY
    cF
    fimacnv
    eqcomd
    syl
    eqtr3d
    difeq1d
    @19
    @4
    cF
    wfun
    @5
    ccnv
    wfun
    @24
    @26
    wceq
    @28
    cX
    cY
    cF
    ffun
    cF
    funcnvcnv
    cY
    @14
    @5
    imadif
    4syl
    eqtr4d
    @19
    @23
    @10
    wcel
    @11
    @24
    @8
    wcel
    #
    @19
    @23
    cK
    cuni
    #
    @14
    cdif
    #
    @10
    @19
    cY
    @30
    @14
    @1
    cY
    @30
    wceq
    @0
    @12
    @18
    cY
    cK
    toponuni
    ad3antlr
    difeq1d
    @13
    @18
    cK
    ctop
    wcel
    #
    @31
    @10
    wcel
    @1
    @32
    @0
    @12
    @18
    cY
    cK
    topontop
    ad3antlr
    @14
    cK
    @30
    @30
    eqid
    opncld
    sylancom
    eqeltrd
    @2
    @4
    @11
    @18
    simplrr
    @9
    @29
    vy
    @23
    @10
    @6
    @23
    wceq
    @7
    @24
    @8
    @6
    @23
    @5
    imaeq2
    eleq1d
    rspcv
    sylc
    eqeltrd
    @19
    cJ
    ctop
    wcel
    #
    @15
    @20
    wss
    @16
    @22
    wb
    @0
    @33
    @1
    @12
    @18
    cX
    cJ
    topontop
    ad3antrrr
    @19
    @15
    cX
    @20
    @19
    cF
    cdm
    #
    @15
    cX
    cF
    @14
    cnvimass
    @19
    @4
    @34
    cX
    wceq
    @28
    cX
    cY
    cF
    fdm
    syl
    syl5sseq
    @27
    sseqtrd
    @15
    cJ
    @20
    @20
    eqid
    isopn2
    syl2anc
    mpbird
    ralrimiva
    @2
    @3
    @4
    @17
    wa
    wb
    @12
    vx
    cF
    cJ
    cK
    cX
    cY
    iscn
    adantr
    mpbir2and
    impbida
end
