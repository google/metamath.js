include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "cqtop.mm"
include "co.mm"
include "ccld.mm"
include "cuni.mm"
include "wss.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "ctop.mm"
include "wb.mm"
include "qtoptopon.mm"
include "topontop.mm"
include "eqid.mm"
include "iscld.mm"
include "3syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "syl.mm"
include "sseq2d.mm"
include "difeq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "elqtop3.mm"
include "adantr.mm"
include "difss.mm"
include "biantrur.mm"
include "wfun.mm"
include "fofun.mm"
include "ad2antlr.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "wf.mm"
include "fof.mm"
include "fimacnv.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "fofn.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "sseqtrd.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "3bitr2d.mm"

theorem qtopcld
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F : X -onto-> Y ) -> ( A e. ( Clsd ` ( J qTop F ) ) <-> ( A C_ Y /\ ( `' F " A ) e. ( Clsd ` J ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    wa
    #
    cA
    cJ
    cF
    cqtop
    co
    #
    ccld
    cfv
    wcel
    #
    cA
    @3
    cuni
    #
    wss
    #
    @5
    cA
    cdif
    #
    @3
    wcel
    #
    wa
    #
    cA
    cY
    wss
    #
    cY
    cA
    cdif
    #
    @3
    wcel
    #
    wa
    @10
    cF
    ccnv
    #
    cA
    cima
    #
    cJ
    ccld
    cfv
    wcel
    #
    wa
    @2
    @3
    cY
    ctopon
    cfv
    wcel
    #
    @3
    ctop
    wcel
    @4
    @9
    wb
    cF
    cJ
    cX
    cY
    qtoptopon
    #
    cY
    @3
    topontop
    cA
    @3
    @5
    @5
    eqid
    iscld
    3syl
    @2
    @10
    @6
    @12
    @8
    @2
    cY
    @5
    cA
    @2
    @16
    cY
    @5
    wceq
    @17
    cY
    @3
    toponuni
    syl
    #
    sseq2d
    @2
    @11
    @7
    @3
    @2
    cY
    @5
    cA
    @18
    difeq1d
    eleq1d
    anbi12d
    @2
    @10
    @12
    @15
    @2
    @10
    wa
    #
    @12
    @11
    cY
    wss
    #
    @13
    @11
    cima
    #
    cJ
    wcel
    #
    wa
    #
    @15
    @2
    @12
    @23
    wb
    @10
    @11
    cF
    cJ
    cX
    cY
    elqtop3
    adantr
    @23
    @22
    @19
    @15
    @20
    @22
    cY
    cA
    difss
    biantrur
    @19
    @22
    cJ
    cuni
    #
    @14
    cdif
    #
    cJ
    wcel
    #
    @15
    @19
    @21
    @25
    cJ
    @19
    @21
    @13
    cY
    cima
    #
    @14
    cdif
    #
    @25
    @19
    cF
    wfun
    #
    @13
    ccnv
    wfun
    @21
    @28
    wceq
    @1
    @29
    @0
    @10
    cX
    cY
    cF
    fofun
    ad2antlr
    cF
    funcnvcnv
    cY
    cA
    @13
    imadif
    3syl
    @19
    @27
    @24
    @14
    @19
    @27
    cX
    @24
    @1
    @27
    cX
    wceq
    #
    @0
    @10
    @1
    cX
    cY
    cF
    wf
    @30
    cX
    cY
    cF
    fof
    cX
    cY
    cF
    fimacnv
    syl
    ad2antlr
    @0
    cX
    @24
    wceq
    @1
    @10
    cX
    cJ
    toponuni
    ad2antrr
    #
    eqtrd
    difeq1d
    eqtrd
    eleq1d
    @19
    cJ
    ctop
    wcel
    #
    @14
    @24
    wss
    @15
    @26
    wb
    @0
    @32
    @1
    @10
    cX
    cJ
    topontop
    ad2antrr
    @19
    @14
    cX
    @24
    @19
    cF
    cdm
    #
    @14
    cX
    cF
    cA
    cnvimass
    @1
    @33
    cX
    wceq
    #
    @0
    @10
    @1
    cF
    cX
    wfn
    @34
    cX
    cY
    cF
    fofn
    cX
    cF
    fndm
    syl
    ad2antlr
    syl5sseq
    @31
    sseqtrd
    @14
    cJ
    @24
    @24
    eqid
    iscld2
    syl2anc
    bitr4d
    syl5bbr
    bitrd
    pm5.32da
    3bitr2d
end
