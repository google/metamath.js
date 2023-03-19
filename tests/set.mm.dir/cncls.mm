include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "ccl.mm"
include "cima.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "cnf2.mm"
include "3expia.mm"
include "cuni.mm"
include "wi.mm"
include "elpwi.mm"
include "adantl.mm"
include "wceq.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cnclsi.mm"
include "expcom.mm"
include "syl.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "ccnv.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "ad2antlr.mm"
include "syl5sseq.mm"
include "wb.mm"
include "toponmax.mm"
include "ad3antrrr.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "fveq2.mm"
include "imaeq2d.mm"
include "imaeq2.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "ctop.mm"
include "topontop.mm"
include "ad3antlr.mm"
include "crn.mm"
include "cin.mm"
include "wfun.mm"
include "ffun.mm"
include "funimacnv.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "clsss.mm"
include "syl3anc.mm"
include "sstr2.mm"
include "syl5com.mm"
include "eqtrd.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "sylibd.mm"
include "syld.mm"
include "imdistanda.mm"
include "cncls2.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem cncls
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vy: setvar y

  disjoint F x
  disjoint J x
  disjoint K x
  disjoint X x
  disjoint Y x
  disjoint x y
  disjoint F y
  disjoint J y
  disjoint K y
  disjoint X y
  disjoint Y y
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. x e. ~P X ( F " ( ( cls ` J ) ` x ) ) C_ ( ( cls ` K ) ` ( F " x ) ) ) ) )

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
    vx
    cv
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cima
    #
    cF
    @5
    cima
    #
    cK
    ccl
    cfv
    #
    cfv
    #
    wss
    #
    vx
    cX
    cpw
    #
    wral
    #
    wa
    #
    @2
    @3
    @4
    @14
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
    3expia
    @2
    @3
    @12
    vx
    @13
    @2
    @5
    @13
    wcel
    #
    wa
    #
    @5
    cJ
    cuni
    #
    wss
    #
    @3
    @12
    wi
    @17
    @5
    cX
    @18
    @16
    @5
    cX
    wss
    @2
    @5
    cX
    elpwi
    adantl
    @0
    cX
    @18
    wceq
    #
    @1
    @16
    cX
    cJ
    toponuni
    #
    ad2antrr
    sseqtrd
    @3
    @19
    @12
    @5
    cF
    cJ
    cK
    @18
    @18
    eqid
    #
    cnclsi
    expcom
    syl
    ralrimdva
    jcad
    @2
    @15
    @4
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    @6
    cfv
    #
    @23
    @24
    @10
    cfv
    #
    cima
    wss
    #
    vy
    cY
    cpw
    #
    wral
    #
    wa
    @3
    @2
    @4
    @14
    @30
    @2
    @4
    wa
    #
    @14
    @28
    vy
    @29
    @31
    @24
    @29
    wcel
    #
    wa
    #
    @14
    cF
    @26
    cima
    #
    cF
    @25
    cima
    #
    @10
    cfv
    #
    wss
    #
    @28
    @33
    @25
    @13
    wcel
    #
    @14
    @37
    wi
    @33
    @38
    @25
    cX
    wss
    #
    @33
    cF
    cdm
    #
    @25
    cX
    cF
    @24
    cnvimass
    #
    @4
    @40
    cX
    wceq
    @2
    @32
    cX
    cY
    cF
    fdm
    ad2antlr
    #
    syl5sseq
    @33
    cX
    cJ
    wcel
    #
    @38
    @39
    wb
    @0
    @43
    @1
    @4
    @32
    cX
    cJ
    toponmax
    ad3antrrr
    @25
    cX
    cJ
    elpw2g
    syl
    mpbird
    @12
    @37
    vx
    @25
    @13
    @5
    @25
    wceq
    #
    @8
    @34
    @11
    @36
    @44
    @7
    @26
    cF
    @5
    @25
    @6
    fveq2
    imaeq2d
    @44
    @9
    @35
    @10
    @5
    @25
    cF
    imaeq2
    fveq2d
    sseq12d
    rspcv
    syl
    @33
    @37
    @34
    @27
    wss
    #
    @28
    @33
    @36
    @27
    wss
    #
    @37
    @45
    @33
    cK
    ctop
    wcel
    #
    @24
    cK
    cuni
    #
    wss
    @35
    @24
    wss
    @46
    @1
    @47
    @0
    @4
    @32
    cY
    cK
    topontop
    ad3antlr
    @33
    @24
    cY
    @48
    @32
    @24
    cY
    wss
    @31
    @24
    cY
    elpwi
    adantl
    @1
    cY
    @48
    wceq
    @0
    @4
    @32
    cY
    cK
    toponuni
    ad3antlr
    sseqtrd
    @33
    @35
    @24
    cF
    crn
    #
    cin
    #
    @24
    @33
    cF
    wfun
    #
    @35
    @50
    wceq
    @4
    @51
    @2
    @32
    cX
    cY
    cF
    ffun
    ad2antlr
    #
    @24
    cF
    funimacnv
    syl
    @24
    @49
    inss1
    syl6eqss
    @24
    @35
    cK
    @48
    @48
    eqid
    clsss
    syl3anc
    @34
    @36
    @27
    sstr2
    syl5com
    @33
    @51
    @26
    @40
    wss
    @45
    @28
    wb
    @52
    @33
    @26
    @18
    @40
    @33
    cJ
    ctop
    wcel
    #
    @25
    @18
    wss
    @26
    @18
    wss
    @0
    @53
    @1
    @4
    @32
    cX
    cJ
    topontop
    ad3antrrr
    @33
    @40
    @25
    @18
    @41
    @33
    @40
    cX
    @18
    @42
    @0
    @20
    @1
    @4
    @32
    @21
    ad3antrrr
    eqtrd
    #
    syl5sseq
    @25
    cJ
    @18
    @22
    clsss3
    syl2anc
    @54
    sseqtr4d
    @26
    @27
    cF
    funimass3
    syl2anc
    sylibd
    syld
    ralrimdva
    imdistanda
    vy
    cF
    cJ
    cK
    cX
    cY
    cncls2
    sylibrd
    impbid
end
