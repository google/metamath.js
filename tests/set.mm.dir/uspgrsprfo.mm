include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "uspgrsprf.mm"
include "a1i.mm"
include "wa.mm"
include "c2nd.mm"
include "cspr.mm"
include "wss.mm"
include "wi.mm"
include "cpw.mm"
include "eleq2i.mm"
include "selpw.mm"
include "bitri.mm"
include "cop.mm"
include "cvtx.mm"
include "cedg.mm"
include "cuspgr.mm"
include "eqidd.mm"
include "cid.mm"
include "cres.mm"
include "cdm.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "wf1o.mm"
include "wex.mm"
include "cvv.mm"
include "vex.mm"
include "f1oi.mm"
include "wb.mm"
include "dmresi.mm"
include "f1oeq2.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "sprvalpwle2.mm"
include "sseq2d.mm"
include "biimpac.mm"
include "jca.mm"
include "weq.mm"
include "f1oeq3.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "elabd.mm"
include "resiexg.mm"
include "f11o.mm"
include "resiexd.mm"
include "anim2i.mm"
include "ancoms.mm"
include "isuspgrop.mm"
include "syl.mm"
include "mpbird.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "opvtxfv.mm"
include "crn.mm"
include "edgopval.mm"
include "rnresi.mm"
include "syl6eq.mm"
include "rspcedvd.mm"
include "copab.mm"
include "anim1i.mm"
include "ancomd.mm"
include "eqeq1.mm"
include "adantr.mm"
include "eqeq2.mm"
include "bi2anan9.mm"
include "rexbidv.mm"
include "opelopabga.mm"
include "syl5bb.mm"
include "eqeq2d.mm"
include "op2ndg.mm"
include "mpan2.mm"
include "eqcomd.mm"
include "ex.mm"
include "sylbi.mm"
include "impcom.mm"
include "uspgrsprfv.mm"
include "rexbidva.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem uspgrsprfo
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vq: setvar q
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }
  assume uspgrsprf.f: |- F = ( g e. G |-> ( 2nd ` g ) )

  disjoint P e
  disjoint P g
  disjoint P v
  disjoint e g
  disjoint e v
  disjoint g v
  disjoint G g
  disjoint V e
  disjoint V v
  disjoint V q
  disjoint W q
  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint W e
  disjoint W v
  disjoint G g
  disjoint X g
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint a g
  disjoint b g
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint V f
  disjoint V w
  disjoint a f
  disjoint a e
  disjoint a v
  disjoint a w
  disjoint b f
  disjoint b e
  disjoint b v
  disjoint b w
  disjoint e f
  disjoint f v
  disjoint f w
  disjoint e w
  disjoint v w
  disjoint f q
  disjoint q w
  disjoint V p
  disjoint a p
  disjoint f p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint a q
  disjoint k x
  assert |- ( V e. W -> F : G -onto-> P )

  proof
    cV
    cW
    wcel
    #
    cG
    cP
    cF
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vb
    cG
    wrex
    #
    va
    cP
    wral
    cG
    cP
    cF
    wfo
    @1
    @0
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprf
    a1i
    @0
    @6
    va
    cP
    @0
    @2
    cP
    wcel
    #
    wa
    #
    @6
    @2
    @3
    c2nd
    cfv
    #
    wceq
    #
    vb
    cG
    wrex
    #
    @7
    @0
    @11
    @7
    @2
    cV
    cspr
    cfv
    #
    wss
    #
    @0
    @11
    wi
    @7
    @2
    @12
    cpw
    #
    wcel
    @13
    cP
    @14
    @2
    uspgrsprf.p
    eleq2i
    va
    @12
    selpw
    bitri
    @13
    @0
    @11
    @13
    @0
    wa
    #
    @10
    @2
    cV
    @2
    cop
    #
    c2nd
    cfv
    #
    wceq
    #
    vb
    @16
    cG
    @15
    @16
    cG
    wcel
    #
    cV
    cV
    wceq
    #
    vq
    cv
    #
    cvtx
    cfv
    #
    cV
    wceq
    #
    @21
    cedg
    cfv
    #
    @2
    wceq
    #
    wa
    #
    vq
    cuspgr
    wrex
    #
    wa
    #
    @15
    @20
    @27
    @15
    cV
    eqidd
    @15
    @26
    cV
    cid
    @2
    cres
    #
    cop
    #
    cvtx
    cfv
    #
    cV
    wceq
    #
    @30
    cedg
    cfv
    #
    @2
    wceq
    #
    wa
    #
    vq
    @30
    cuspgr
    @15
    @30
    cuspgr
    wcel
    #
    @29
    cdm
    #
    vp
    cv
    chash
    cfv
    c2
    cle
    wbr
    vp
    cV
    cpw
    c0
    csn
    cdif
    crab
    #
    @29
    wf1
    #
    @15
    @37
    vf
    cv
    #
    @29
    wf1o
    #
    @40
    @38
    wss
    #
    wa
    #
    vf
    wex
    @39
    @15
    @43
    @37
    @2
    @29
    wf1o
    #
    @2
    @38
    wss
    #
    wa
    vf
    @2
    @2
    cvv
    wcel
    #
    @15
    va
    vex
    #
    a1i
    @15
    @44
    @45
    @15
    @2
    @2
    @29
    wf1o
    #
    @44
    @48
    @15
    @2
    f1oi
    a1i
    @37
    @2
    wceq
    @44
    @48
    wb
    @2
    dmresi
    @37
    @2
    @2
    @29
    f1oeq2
    ax-mp
    sylibr
    @0
    @13
    @45
    @0
    @12
    @38
    @2
    cV
    cW
    vp
    sprvalpwle2
    sseq2d
    biimpac
    jca
    vf
    va
    weq
    @41
    @44
    @42
    @45
    @40
    @2
    @37
    @29
    f1oeq3
    @40
    @2
    @38
    sseq1
    anbi12d
    elabd
    vf
    @37
    @38
    @29
    @46
    @29
    cvv
    wcel
    #
    @47
    @2
    cvv
    resiexg
    ax-mp
    f11o
    sylibr
    @15
    @0
    @49
    wa
    #
    @36
    @39
    wb
    @0
    @13
    @50
    @13
    @49
    @0
    @13
    @2
    cvv
    @46
    @13
    @47
    a1i
    #
    resiexd
    anim2i
    #
    ancoms
    @29
    cV
    cW
    cvv
    vp
    isuspgrop
    syl
    mpbird
    @21
    @30
    wceq
    #
    @26
    @35
    wb
    @15
    @53
    @23
    @32
    @25
    @34
    @53
    @22
    @31
    cV
    @21
    @30
    cvtx
    fveq2
    eqeq1d
    @53
    @24
    @33
    @2
    @21
    @30
    cedg
    fveq2
    eqeq1d
    anbi12d
    adantl
    @0
    @13
    @35
    @0
    @13
    wa
    #
    @32
    @34
    @54
    @50
    @32
    @52
    @29
    cV
    cW
    cvv
    opvtxfv
    syl
    @54
    @33
    @29
    crn
    #
    @2
    @54
    @50
    @33
    @55
    wceq
    @52
    @29
    cV
    cW
    cvv
    edgopval
    syl
    @2
    rnresi
    syl6eq
    jca
    ancoms
    rspcedvd
    jca
    @19
    @16
    vv
    cv
    #
    cV
    wceq
    #
    @22
    @56
    wceq
    #
    @24
    ve
    cv
    #
    wceq
    #
    wa
    #
    vq
    cuspgr
    wrex
    #
    wa
    #
    vv
    ve
    copab
    #
    wcel
    #
    @15
    @28
    cG
    @64
    @16
    uspgrsprf.g
    eleq2i
    @15
    @0
    @46
    wa
    @65
    @28
    wb
    @15
    @46
    @0
    @13
    @46
    @0
    @51
    anim1i
    ancomd
    @63
    @28
    vv
    ve
    cV
    @2
    cW
    cvv
    @57
    ve
    va
    weq
    #
    wa
    #
    @57
    @20
    @62
    @27
    @57
    @57
    @20
    wb
    @66
    @56
    cV
    cV
    eqeq1
    adantr
    @67
    @61
    @26
    vq
    cuspgr
    @57
    @58
    @23
    @66
    @60
    @25
    @56
    cV
    @22
    eqeq2
    @59
    @2
    @24
    eqeq2
    bi2anan9
    rexbidv
    anbi12d
    opelopabga
    syl
    syl5bb
    mpbird
    @3
    @16
    wceq
    #
    @10
    @18
    wb
    @15
    @68
    @9
    @17
    @2
    @3
    @16
    c2nd
    fveq2
    eqeq2d
    adantl
    @15
    @17
    @2
    @0
    @17
    @2
    wceq
    #
    @13
    @0
    @46
    @69
    @47
    cV
    @2
    cW
    cvv
    op2ndg
    mpan2
    adantl
    eqcomd
    rspcedvd
    ex
    sylbi
    impcom
    @8
    @5
    @10
    vb
    cG
    @8
    @3
    cG
    wcel
    #
    wa
    @4
    @9
    @2
    @70
    @4
    @9
    wceq
    @8
    vv
    cP
    ve
    vg
    cF
    cG
    cV
    @3
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrsprf.f
    uspgrsprfv
    adantl
    eqeq2d
    rexbidva
    mpbird
    ralrimiva
    vb
    va
    cG
    cP
    cF
    dffo3
    sylanbrc
end
