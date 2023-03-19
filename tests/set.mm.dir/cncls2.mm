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
include "ccl.mm"
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
include "ad2antlr.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cncls2i.mm"
include "expcom.mm"
include "syl.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "ccld.mm"
include "cldss2.mm"
include "pweqd.mm"
include "syl5sseqr.mm"
include "sseld.mm"
include "imim1d.mm"
include "wb.mm"
include "cldcls.mm"
include "ad2antll.mm"
include "imaeq2d.mm"
include "sseq2d.mm"
include "ctop.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "ad2antrl.mm"
include "eqtrd.mm"
include "syl5sseq.mm"
include "iscld4.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "expr.mm"
include "pm5.74d.mm"
include "sylibd.mm"
include "ralimdv2.mm"
include "imdistanda.mm"
include "iscncl.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem cncls2
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
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. x e. ~P Y ( ( cls ` J ) ` ( `' F " x ) ) C_ ( `' F " ( ( cls ` K ) ` x ) ) ) ) )

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
    vx
    cv
    #
    cima
    #
    cJ
    ccl
    cfv
    cfv
    #
    @5
    @6
    cK
    ccl
    cfv
    cfv
    #
    cima
    #
    wss
    #
    vx
    cY
    cpw
    #
    wral
    #
    wa
    #
    @2
    @3
    @4
    @13
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
    @11
    vx
    @12
    @2
    @6
    @12
    wcel
    #
    wa
    #
    @6
    cK
    cuni
    #
    wss
    #
    @3
    @11
    wi
    @16
    @6
    cY
    @17
    @15
    @6
    cY
    wss
    @2
    @6
    cY
    elpwi
    adantl
    @1
    cY
    @17
    wceq
    #
    @0
    @15
    cY
    cK
    toponuni
    #
    ad2antlr
    sseqtrd
    @3
    @18
    @11
    @6
    cF
    cJ
    cK
    @17
    @17
    eqid
    #
    cncls2i
    expcom
    syl
    ralrimdva
    jcad
    @2
    @14
    @4
    @7
    cJ
    ccld
    cfv
    wcel
    #
    vx
    cK
    ccld
    cfv
    #
    wral
    #
    wa
    @3
    @2
    @4
    @13
    @24
    @2
    @4
    wa
    #
    @11
    @22
    vx
    @12
    @23
    @25
    @15
    @11
    wi
    @6
    @23
    wcel
    #
    @11
    wi
    @26
    @22
    wi
    @25
    @26
    @15
    @11
    @25
    @23
    @12
    @6
    @25
    @17
    cpw
    @23
    @12
    cK
    @17
    @21
    cldss2
    @25
    cY
    @17
    @1
    @19
    @0
    @4
    @20
    ad2antlr
    pweqd
    syl5sseqr
    sseld
    imim1d
    @25
    @26
    @11
    @22
    @2
    @4
    @26
    @11
    @22
    wb
    @2
    @4
    @26
    wa
    #
    wa
    #
    @11
    @8
    @7
    wss
    #
    @22
    @28
    @10
    @7
    @8
    @28
    @9
    @6
    @5
    @26
    @9
    @6
    wceq
    @2
    @4
    @6
    cK
    cldcls
    ad2antll
    imaeq2d
    sseq2d
    @28
    cJ
    ctop
    wcel
    #
    @7
    cJ
    cuni
    #
    wss
    @22
    @29
    wb
    @0
    @30
    @1
    @27
    cX
    cJ
    topontop
    ad2antrr
    @28
    cF
    cdm
    #
    @7
    @31
    cF
    @6
    cnvimass
    @28
    @32
    cX
    @31
    @4
    @32
    cX
    wceq
    @2
    @26
    cX
    cY
    cF
    fdm
    ad2antrl
    @0
    cX
    @31
    wceq
    @1
    @27
    cX
    cJ
    toponuni
    ad2antrr
    eqtrd
    syl5sseq
    @7
    cJ
    @31
    @31
    eqid
    iscld4
    syl2anc
    bitr4d
    expr
    pm5.74d
    sylibd
    ralimdv2
    imdistanda
    vx
    cF
    cJ
    cK
    cX
    cY
    iscncl
    sylibrd
    impbid
end
