include "cgr.mm"
include "wcel.mm"
include "cghomOLD.mm"
include "co.mm"
include "w3a.mm"
include "wf1.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "ghomidOLD.mm"
include "sneqd.mm"
include "wfn.mm"
include "wf.mm"
include "ghomf.mm"
include "ffn.mm"
include "syl.mm"
include "grpoidcl.mm"
include "3ad2ant1.mm"
include "fnsnfv.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "imaeq2d.mm"
include "adantl.mm"
include "wss.mm"
include "snssd.mm"
include "f1imacnv.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "expcom.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "adantr.mm"
include "cgs.mm"
include "wb.mm"
include "simpl2.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqid.mm"
include "grpoeqdivid.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "ghomdiv.mm"
include "eqeq1d.mm"
include "cgi.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snid.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "grpodivcl.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "eleq2.mm"
include "sylan9bb.mm"
include "an32s.mm"
include "elsni.mm"
include "biimprd.mm"
include "syl5.mm"
include "sylbid.mm"
include "sylbird.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid.mm"

theorem grpokerinj
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume grpkerinj.1: |- X = ran G
  assume grpkerinj.2: |- W = ( GId ` G )
  assume grpkerinj.3: |- Y = ran H
  assume grpkerinj.4: |- U = ( GId ` H )


  assert |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) -> ( F : X -1-1-> Y <-> ( `' F " { U } ) = { W } ) )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cF
    cG
    cH
    cghomOLD
    co
    wcel
    #
    w3a
    #
    cX
    cY
    cF
    wf1
    #
    cF
    ccnv
    #
    cU
    csn
    #
    cima
    #
    cW
    csn
    #
    wceq
    #
    @4
    @3
    @9
    @4
    @3
    wa
    @7
    @5
    cF
    @8
    cima
    #
    cima
    #
    @8
    @3
    @7
    @11
    wceq
    @4
    @3
    @6
    @10
    @5
    @3
    cW
    cF
    cfv
    #
    csn
    #
    @6
    @10
    @3
    @12
    cU
    cU
    cW
    cF
    cG
    cH
    grpkerinj.2
    grpkerinj.4
    ghomidOLD
    sneqd
    @3
    cF
    cX
    wfn
    #
    cW
    cX
    wcel
    #
    @13
    @10
    wceq
    @3
    cX
    cY
    cF
    wf
    #
    @14
    cF
    cG
    cH
    cY
    cX
    grpkerinj.1
    grpkerinj.3
    ghomf
    #
    cX
    cY
    cF
    ffn
    syl
    @0
    @1
    @15
    @2
    cW
    cG
    cX
    grpkerinj.1
    grpkerinj.2
    grpoidcl
    #
    3ad2ant1
    cX
    cW
    cF
    fnsnfv
    syl2anc
    eqtr3d
    imaeq2d
    adantl
    @3
    @4
    @8
    cX
    wss
    #
    @11
    @8
    wceq
    @0
    @1
    @19
    @2
    @0
    cW
    cX
    @18
    snssd
    3ad2ant1
    cX
    cY
    @8
    cF
    f1imacnv
    sylan2
    eqtrd
    expcom
    @3
    @9
    @4
    @3
    @9
    wa
    #
    @16
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @21
    @23
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @4
    @3
    @16
    @9
    @17
    adantr
    @20
    @27
    vx
    vy
    cX
    cX
    @20
    @21
    cX
    wcel
    #
    @23
    cX
    wcel
    #
    wa
    #
    wa
    #
    @25
    @22
    @24
    cH
    cgs
    cfv
    #
    co
    #
    cU
    wceq
    #
    @26
    @3
    @30
    @25
    @34
    wb
    #
    @9
    @3
    @30
    wa
    #
    @1
    @22
    cY
    wcel
    #
    @24
    cY
    wcel
    #
    @35
    @0
    @1
    @2
    @30
    simpl2
    @3
    @28
    @37
    @29
    @3
    cX
    cY
    @21
    cF
    @17
    ffvelrnda
    adantrr
    @3
    @29
    @38
    @28
    @3
    cX
    cY
    @23
    cF
    @17
    ffvelrnda
    adantrl
    @22
    @24
    @32
    cU
    cH
    cY
    grpkerinj.3
    grpkerinj.4
    @32
    eqid
    #
    grpoeqdivid
    syl3anc
    adantlr
    @31
    @34
    @21
    @23
    cG
    cgs
    cfv
    #
    co
    #
    cF
    cfv
    #
    cU
    wceq
    #
    @26
    @31
    @42
    @33
    cU
    @3
    @30
    @42
    @33
    wceq
    @9
    @21
    @23
    @32
    @40
    cF
    cG
    cH
    cX
    grpkerinj.1
    @40
    eqid
    #
    @39
    ghomdiv
    adantlr
    eqeq1d
    @43
    @42
    @6
    wcel
    #
    @31
    @26
    @43
    @45
    cU
    @6
    wcel
    cU
    cU
    cH
    cgi
    cfv
    cvv
    grpkerinj.4
    cH
    cgi
    fvex
    eqeltri
    snid
    @42
    cU
    @6
    eleq1
    mpbiri
    @31
    @45
    @41
    @8
    wcel
    #
    @26
    @3
    @30
    @9
    @45
    @46
    wb
    @36
    @45
    @41
    @7
    wcel
    #
    @9
    @46
    @36
    cF
    wfun
    #
    @41
    cF
    cdm
    #
    wcel
    @45
    @47
    wb
    @3
    @48
    @30
    @3
    @16
    @48
    @17
    cX
    cY
    cF
    ffun
    syl
    adantr
    @36
    @41
    cX
    @49
    @0
    @1
    @30
    @41
    cX
    wcel
    #
    @2
    @0
    @28
    @29
    @50
    @21
    @23
    @40
    cG
    cX
    grpkerinj.1
    @44
    grpodivcl
    3expb
    3ad2antl1
    @3
    @49
    cX
    wceq
    #
    @30
    @3
    @16
    @51
    @17
    cX
    cY
    cF
    fdm
    syl
    adantr
    eleqtrrd
    @41
    @6
    cF
    fvimacnv
    syl2anc
    @7
    @8
    @41
    eleq2
    sylan9bb
    an32s
    @3
    @30
    @46
    @26
    wi
    @9
    @46
    @41
    cW
    wceq
    #
    @36
    @26
    @41
    cW
    elsni
    @0
    @1
    @30
    @52
    @26
    wi
    #
    @2
    @0
    @28
    @29
    @53
    @0
    @28
    @29
    w3a
    @26
    @52
    @21
    @23
    @40
    cW
    cG
    cX
    grpkerinj.1
    grpkerinj.2
    @44
    grpoeqdivid
    biimprd
    3expb
    3ad2antl1
    syl5
    adantlr
    sylbid
    syl5
    sylbird
    sylbid
    ralrimivva
    vx
    vy
    cX
    cY
    cF
    dff13
    sylanbrc
    ex
    impbid
end
