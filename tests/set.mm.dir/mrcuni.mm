include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "cima.mm"
include "simpl.mm"
include "cv.mm"
include "wral.mm"
include "simpll.mm"
include "ssel2.mm"
include "elpwid.mm"
include "adantll.mm"
include "mrcssid.mm"
include "syl2anc.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "wf.mm"
include "mrcf.mm"
include "ffun.mm"
include "syl.mm"
include "adantr.mm"
include "wceq.mm"
include "fdm.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "funfvima2.mm"
include "imp.mm"
include "elssuni.mm"
include "sstrd.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "sylibr.mm"
include "mrcssv.mm"
include "ralrimivw.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "sseq1.mm"
include "ralima.mm"
include "sylan.mm"
include "mpbird.mm"
include "mrcss.mm"
include "syl3anc.mm"
include "adantl.mm"
include "sspwuni.mm"
include "biimpi.mm"
include "mrcidm.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem mrcuni
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ ~P X ) -> ( F ` U. U ) = ( F ` U. ( F " U ) ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cX
    cpw
    #
    wss
    #
    wa
    #
    cU
    cuni
    #
    cF
    cfv
    #
    cF
    cU
    cima
    #
    cuni
    #
    cF
    cfv
    #
    @3
    @0
    @4
    @7
    wss
    #
    @7
    cX
    wss
    #
    @5
    @8
    wss
    @0
    @2
    simpl
    #
    @3
    vs
    cv
    #
    @7
    wss
    #
    vs
    cU
    wral
    @9
    @3
    @13
    vs
    cU
    @3
    @12
    cU
    wcel
    #
    wa
    #
    @12
    @12
    cF
    cfv
    #
    @7
    @15
    @0
    @12
    cX
    wss
    #
    @12
    @16
    wss
    @0
    @2
    @14
    simpll
    @2
    @14
    @17
    @0
    @2
    @14
    wa
    @12
    cX
    cU
    @1
    @12
    ssel2
    elpwid
    adantll
    cC
    @12
    cF
    cX
    mrcfval.f
    mrcssid
    syl2anc
    @15
    @16
    @6
    wcel
    #
    @16
    @7
    wss
    @3
    @14
    @18
    @3
    cF
    wfun
    #
    cU
    cF
    cdm
    #
    wss
    #
    @14
    @18
    wi
    @0
    @19
    @2
    @0
    @1
    cC
    cF
    wf
    #
    @19
    cC
    cF
    cX
    mrcfval.f
    mrcf
    #
    @1
    cC
    cF
    ffun
    syl
    adantr
    @0
    @21
    @2
    @0
    @20
    @1
    cU
    @0
    @22
    @20
    @1
    wceq
    @23
    @1
    cC
    cF
    fdm
    syl
    sseq2d
    biimpar
    cU
    @12
    cF
    funfvima2
    syl2anc
    imp
    @16
    @6
    elssuni
    syl
    sstrd
    ralrimiva
    vs
    cU
    @7
    unissb
    sylibr
    @3
    @17
    vs
    @6
    wral
    #
    @10
    @3
    @24
    vx
    cv
    #
    cF
    cfv
    #
    cX
    wss
    #
    vx
    cU
    wral
    #
    @3
    @27
    vx
    cU
    @0
    @27
    @2
    cC
    @25
    cF
    cX
    mrcfval.f
    mrcssv
    adantr
    ralrimivw
    @0
    cF
    @1
    wfn
    #
    @2
    @24
    @28
    wb
    @0
    @22
    @29
    @23
    @1
    cC
    cF
    ffn
    syl
    #
    @17
    @27
    vs
    vx
    @1
    cU
    cF
    @12
    @26
    cX
    sseq1
    ralima
    sylan
    mpbird
    vs
    @6
    cX
    unissb
    sylibr
    cC
    @4
    cF
    @7
    cX
    mrcfval.f
    mrcss
    syl3anc
    @3
    @8
    @5
    cF
    cfv
    #
    @5
    @3
    @0
    @7
    @5
    wss
    #
    @5
    cX
    wss
    #
    @8
    @31
    wss
    @11
    @3
    @12
    @5
    wss
    #
    vs
    @6
    wral
    #
    @32
    @3
    @35
    @26
    @5
    wss
    #
    vx
    cU
    wral
    #
    @3
    @36
    vx
    cU
    @3
    @25
    cU
    wcel
    #
    wa
    @0
    @25
    @4
    wss
    #
    @4
    cX
    wss
    #
    @36
    @0
    @2
    @38
    simpll
    @38
    @39
    @3
    @25
    cU
    elssuni
    adantl
    @3
    @40
    @38
    @2
    @40
    @0
    @2
    @40
    cU
    cX
    sspwuni
    biimpi
    adantl
    #
    adantr
    cC
    @25
    cF
    @4
    cX
    mrcfval.f
    mrcss
    syl3anc
    ralrimiva
    @0
    @29
    @2
    @35
    @37
    wb
    @30
    @34
    @36
    vs
    vx
    @1
    cU
    cF
    @12
    @26
    @5
    sseq1
    ralima
    sylan
    mpbird
    vs
    @6
    @5
    unissb
    sylibr
    @0
    @33
    @2
    cC
    @4
    cF
    cX
    mrcfval.f
    mrcssv
    adantr
    cC
    @7
    cF
    @5
    cX
    mrcfval.f
    mrcss
    syl3anc
    @3
    @0
    @40
    @31
    @5
    wceq
    @11
    @41
    cC
    @4
    cF
    cX
    mrcfval.f
    mrcidm
    syl2anc
    sseqtrd
    eqssd
end
