include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cnt.mm"
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
include "ad2antlr.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cnntri.mm"
include "expcom.mm"
include "syl.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "toponss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ex.mm"
include "imim1d.mm"
include "wb.mm"
include "ctop.mm"
include "topontop.mm"
include "ad3antrrr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "eqtrd.mm"
include "syl5sseq.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "eqss.mm"
include "baib.mm"
include "isopn3.mm"
include "ad3antlr.mm"
include "isopn3i.mm"
include "sylancom.mm"
include "imaeq2d.mm"
include "sseq1d.mm"
include "3bitr4rd.mm"
include "pm5.74da.mm"
include "sylibd.mm"
include "ralimdv2.mm"
include "imdistanda.mm"
include "iscn.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem cnntr
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
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. x e. ~P Y ( `' F " ( ( int ` K ) ` x ) ) C_ ( ( int ` J ) ` ( `' F " x ) ) ) ) )

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
    cK
    cnt
    cfv
    cfv
    #
    cima
    #
    @5
    @6
    cima
    #
    cJ
    cnt
    cfv
    cfv
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
    #
    @2
    @6
    cY
    elpwi
    adantl
    @1
    cY
    @17
    wceq
    @0
    @15
    cY
    cK
    toponuni
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
    cnntri
    expcom
    syl
    ralrimdva
    jcad
    @2
    @14
    @4
    @9
    cJ
    wcel
    #
    vx
    cK
    wral
    #
    wa
    @3
    @2
    @4
    @13
    @21
    @2
    @4
    wa
    #
    @11
    @20
    vx
    @12
    cK
    @22
    @15
    @11
    wi
    @6
    cK
    wcel
    #
    @11
    wi
    @23
    @20
    wi
    @22
    @23
    @15
    @11
    @1
    @23
    @15
    wi
    @0
    @4
    @1
    @23
    @15
    @1
    @23
    wa
    @19
    @15
    @6
    cK
    cY
    toponss
    vx
    cY
    selpw
    sylibr
    ex
    ad2antlr
    imim1d
    @22
    @23
    @11
    @20
    @22
    @23
    wa
    #
    @10
    @9
    wceq
    #
    @9
    @10
    wss
    #
    @20
    @11
    @24
    @10
    @9
    wss
    #
    @25
    @26
    wb
    @24
    cJ
    ctop
    wcel
    #
    @9
    cJ
    cuni
    #
    wss
    #
    @27
    @0
    @28
    @1
    @4
    @23
    cX
    cJ
    topontop
    ad3antrrr
    #
    @24
    cF
    cdm
    #
    @9
    @29
    cF
    @6
    cnvimass
    @24
    @32
    cX
    @29
    @4
    @32
    cX
    wceq
    @2
    @23
    cX
    cY
    cF
    fdm
    ad2antlr
    @0
    cX
    @29
    wceq
    @1
    @4
    @23
    cX
    cJ
    toponuni
    ad3antrrr
    eqtrd
    syl5sseq
    #
    @9
    cJ
    @29
    @29
    eqid
    #
    ntrss2
    syl2anc
    @25
    @27
    @26
    @10
    @9
    eqss
    baib
    syl
    @24
    @28
    @30
    @20
    @25
    wb
    @31
    @33
    @9
    cJ
    @29
    @34
    isopn3
    syl2anc
    @24
    @8
    @9
    @10
    @24
    @7
    @6
    @5
    @22
    @23
    cK
    ctop
    wcel
    #
    @7
    @6
    wceq
    @1
    @35
    @0
    @4
    @23
    cY
    cK
    topontop
    ad3antlr
    @6
    cK
    isopn3i
    sylancom
    imaeq2d
    sseq1d
    3bitr4rd
    pm5.74da
    sylibd
    ralimdv2
    imdistanda
    vx
    cF
    cJ
    cK
    cX
    cY
    iscn
    sylibrd
    impbid
end
