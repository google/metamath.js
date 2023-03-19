include "wcel.mm"
include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "cixp.mm"
include "wrex.mm"
include "cq.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "cop.mm"
include "ffvelrnda.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fmptdf.mm"
include "cvv.mm"
include "wb.mm"
include "qex.mm"
include "xpex.mm"
include "a1i.mm"
include "jca.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbird.mm"
include "hoi2toco.mm"
include "sstrd.mm"
include "eqsstrd.mm"
include "wceq.mm"
include "nfcv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfeq.mm"
include "coeq2.mm"
include "fveq1d.mm"
include "adantr.mm"
include "ixpeq2d.mm"
include "sseq1d.mm"
include "elrab2.mm"
include "sylibr.mm"
include "eleqtrrd.mm"
include "nfv.mm"
include "crab.mm"
include "nfrab1.mm"
include "eleq2d.mm"
include "rspcef.mm"

theorem opnvonmbllem1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume opnvonmbllem1.i: |- F/ i ph
  assume opnvonmbllem1.x: |- ( ph -> X e. V )
  assume opnvonmbllem1.c: |- ( ph -> C : X --> QQ )
  assume opnvonmbllem1.d: |- ( ph -> D : X --> QQ )
  assume opnvonmbllem1.s: |- ( ph -> X_ i e. X ( ( C ` i ) [,) ( D ` i ) ) C_ B )
  assume opnvonmbllem1.g: |- ( ph -> B C_ G )
  assume opnvonmbllem1.y: |- ( ph -> Y e. X_ i e. X ( ( C ` i ) [,) ( D ` i ) ) )
  assume opnvonmbllem1.k: |- K = { h e. ( ( QQ X. QQ ) ^m X ) | X_ i e. X ( ( [,) o. h ) ` i ) C_ G }
  assume opnvonmbllem1.h: |- H = ( i e. X |-> <. ( C ` i ) , ( D ` i ) >. )

  disjoint G h
  disjoint H h
  disjoint X h
  disjoint X i
  disjoint h i
  disjoint Y h
  disjoint k x
  assert |- ( ph -> E. h e. K Y e. X_ i e. X ( ( [,) o. h ) ` i ) )

  proof
    wph
    cH
    cK
    wcel
    #
    cY
    vi
    cX
    vi
    cv
    #
    cico
    cH
    ccom
    #
    cfv
    #
    cixp
    #
    wcel
    #
    cY
    vi
    cX
    @1
    cico
    vh
    cv
    #
    ccom
    #
    cfv
    #
    cixp
    #
    wcel
    #
    vh
    cK
    wrex
    wph
    cH
    cq
    cq
    cxp
    #
    cX
    cmap
    co
    #
    wcel
    #
    @4
    cG
    wss
    #
    wa
    @0
    wph
    @13
    @14
    wph
    @13
    cX
    @11
    cH
    wf
    #
    wph
    vi
    cX
    @1
    cC
    cfv
    #
    @1
    cD
    cfv
    #
    cop
    #
    @11
    cH
    opnvonmbllem1.i
    wph
    @1
    cX
    wcel
    #
    wa
    @16
    cq
    wcel
    @17
    cq
    wcel
    @18
    @11
    wcel
    wph
    cX
    cq
    @1
    cC
    opnvonmbllem1.c
    ffvelrnda
    wph
    cX
    cq
    @1
    cD
    opnvonmbllem1.d
    ffvelrnda
    @16
    @17
    cq
    cq
    opelxpi
    syl2anc
    opnvonmbllem1.h
    fmptdf
    wph
    @11
    cvv
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    @13
    @15
    wb
    wph
    @20
    @21
    @20
    wph
    cq
    cq
    qex
    qex
    xpex
    a1i
    opnvonmbllem1.x
    jca
    @11
    cX
    cH
    cvv
    cV
    elmapg
    syl
    mpbird
    wph
    @4
    vi
    cX
    @16
    @17
    cico
    co
    cixp
    #
    cG
    wph
    cC
    cD
    vi
    cH
    cX
    opnvonmbllem1.i
    opnvonmbllem1.h
    hoi2toco
    #
    wph
    @22
    cB
    cG
    opnvonmbllem1.s
    opnvonmbllem1.g
    sstrd
    eqsstrd
    jca
    @9
    cG
    wss
    #
    @14
    vh
    cH
    @12
    cK
    @6
    cH
    wceq
    #
    @9
    @4
    cG
    @25
    vi
    cX
    @8
    @3
    vi
    @6
    cH
    vi
    @6
    nfcv
    vi
    cH
    vi
    cX
    @18
    cmpt
    opnvonmbllem1.h
    vi
    cX
    @18
    nfmpt1
    nfcxfr
    nfeq
    @25
    @8
    @3
    wceq
    @19
    @25
    @1
    @7
    @2
    @6
    cH
    cico
    coeq2
    fveq1d
    adantr
    ixpeq2d
    #
    sseq1d
    opnvonmbllem1.k
    elrab2
    sylibr
    wph
    cY
    @22
    @4
    opnvonmbllem1.y
    @23
    eleqtrrd
    @10
    @5
    vh
    cH
    cK
    @5
    vh
    nfv
    vh
    cH
    nfcv
    vh
    cK
    @24
    vh
    @12
    crab
    opnvonmbllem1.k
    @24
    vh
    @12
    nfrab1
    nfcxfr
    @25
    @9
    @4
    cY
    @26
    eleq2d
    rspcef
    syl2anc
end
