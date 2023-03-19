include "csn.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "snssd.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "ccntz.mm"
include "eqid.mm"
include "csubmnd.mm"
include "cmrc.mm"
include "wss.mm"
include "crn.mm"
include "cress.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cplusg.mm"
include "wceq.mm"
include "ffvelrnd.mm"
include "eqidd.mm"
include "wa.mm"
include "wb.mm"
include "elcntzsn.mm"
include "syl.mm"
include "mpbir2and.mm"
include "cntzspan.mm"
include "syl2anc.mm"
include "cmre.mm"
include "cacs.mm"
include "submacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "mrccl.mm"
include "submcmn2.mm"
include "mpbid.mm"
include "wf.mm"
include "wfn.mm"
include "wral.mm"
include "ffn.mm"
include "simpr.mm"
include "fveq2d.mm"
include "mrcssidd.mm"
include "fvex.mm"
include "snss.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsn.mm"
include "cvv.mm"
include "c0g.mm"
include "eqeltri.mm"
include "a1i.mm"
include "suppssr.mm"
include "sylan2br.mm"
include "subm0cl.mm"
include "adantr.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "cntzidss.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "ffun.mm"
include "snfi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "fex.mm"
include "isfsupp.mm"
include "gsumzres.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "3eqtr3d.mm"

theorem gsumpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  assume gsumpt.b: |- B = ( Base ` G )
  assume gsumpt.z: |- .0. = ( 0g ` G )
  assume gsumpt.g: |- ( ph -> G e. Mnd )
  assume gsumpt.a: |- ( ph -> A e. V )
  assume gsumpt.x: |- ( ph -> X e. A )
  assume gsumpt.f: |- ( ph -> F : A --> B )
  assume gsumpt.s: |- ( ph -> ( F supp .0. ) C_ { X } )


  assert |- ( ph -> ( G gsum F ) = ( F ` X ) )

  proof
    wph
    cG
    cF
    cX
    csn
    #
    cres
    #
    cgsu
    co
    cG
    va
    @0
    va
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
    cX
    cF
    cfv
    #
    wph
    @1
    @4
    cG
    cgsu
    wph
    va
    cA
    cB
    @0
    cF
    gsumpt.f
    wph
    cX
    cA
    gsumpt.x
    snssd
    feqresmpt
    oveq2d
    wph
    cA
    cB
    cF
    cG
    cV
    @0
    c.0
    cG
    ccntz
    cfv
    #
    gsumpt.b
    gsumpt.z
    @7
    eqid
    #
    gsumpt.g
    gsumpt.a
    gsumpt.f
    wph
    @6
    csn
    #
    cG
    csubmnd
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    @12
    @7
    cfv
    wss
    #
    cF
    crn
    #
    @12
    wss
    #
    @14
    @14
    @7
    cfv
    wss
    wph
    cG
    @12
    cress
    co
    #
    ccmn
    wcel
    #
    @13
    wph
    cG
    cmnd
    wcel
    #
    @9
    @9
    @7
    cfv
    #
    wss
    @17
    gsumpt.g
    wph
    @6
    @19
    wph
    @6
    @19
    wcel
    #
    @6
    cB
    wcel
    #
    @6
    @6
    cG
    cplusg
    cfv
    #
    co
    #
    @23
    wceq
    #
    wph
    cA
    cB
    cX
    cF
    gsumpt.f
    gsumpt.x
    ffvelrnd
    #
    wph
    @23
    eqidd
    wph
    @21
    @20
    @21
    @24
    wa
    wb
    @25
    cB
    @22
    cG
    @6
    @6
    @7
    gsumpt.b
    @22
    eqid
    @8
    elcntzsn
    syl
    mpbir2and
    snssd
    @9
    cG
    @16
    @11
    @7
    @8
    @11
    eqid
    #
    @16
    eqid
    #
    cntzspan
    syl2anc
    wph
    @12
    @10
    wcel
    #
    @17
    @13
    wb
    wph
    @10
    cB
    cmre
    cfv
    wcel
    #
    @9
    cB
    wss
    @28
    wph
    @18
    @10
    cB
    cacs
    cfv
    wcel
    @29
    gsumpt.g
    cB
    cG
    gsumpt.b
    submacs
    @10
    cB
    acsmre
    3syl
    #
    wph
    @6
    cB
    @25
    snssd
    #
    @10
    @9
    @11
    cB
    @26
    mrccl
    syl2anc
    #
    @12
    cG
    @16
    @7
    @27
    @8
    submcmn2
    syl
    mpbid
    wph
    cA
    @12
    cF
    wf
    #
    @15
    wph
    cF
    cA
    wfn
    #
    @3
    @12
    wcel
    #
    va
    cA
    wral
    @33
    wph
    cA
    cB
    cF
    wf
    #
    @34
    gsumpt.f
    cA
    cB
    cF
    ffn
    syl
    wph
    @35
    va
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @35
    @2
    cX
    @38
    @2
    cX
    wceq
    #
    wa
    #
    @3
    @6
    @12
    @40
    @2
    cX
    cF
    @38
    @39
    simpr
    fveq2d
    wph
    @6
    @12
    wcel
    #
    @37
    @39
    wph
    @9
    @12
    wss
    @41
    wph
    @10
    @9
    @11
    cB
    @30
    @26
    @31
    mrcssidd
    @6
    @12
    cX
    cF
    fvex
    snss
    sylibr
    ad2antrr
    eqeltrd
    wph
    @37
    @2
    cX
    wne
    #
    @35
    wph
    @37
    @42
    wa
    #
    wa
    @3
    c.0
    @12
    @43
    wph
    @2
    cA
    @0
    cdif
    wcel
    @3
    c.0
    wceq
    @2
    cA
    cX
    eldifsn
    wph
    cA
    cB
    cvv
    cF
    cV
    @0
    @2
    c.0
    gsumpt.f
    gsumpt.s
    gsumpt.a
    c.0
    cvv
    wcel
    #
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumpt.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    #
    suppssr
    sylan2br
    wph
    c.0
    @12
    wcel
    #
    @43
    wph
    @28
    @46
    @32
    @12
    cG
    c.0
    gsumpt.z
    subm0cl
    syl
    adantr
    eqeltrd
    anassrs
    pm2.61dane
    ralrimiva
    va
    cA
    @12
    cF
    ffnfv
    sylanbrc
    cA
    @12
    cF
    frn
    syl
    @12
    @14
    cG
    @7
    @8
    cntzidss
    syl2anc
    gsumpt.s
    wph
    cF
    c.0
    cfsupp
    wbr
    #
    cF
    wfun
    #
    cF
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    @36
    @48
    gsumpt.f
    cA
    cB
    cF
    ffun
    syl
    wph
    @0
    cfn
    wcel
    @49
    @0
    wss
    @50
    cX
    snfi
    gsumpt.s
    @0
    @49
    ssfi
    sylancr
    wph
    cF
    cvv
    wcel
    #
    @44
    @47
    @48
    @50
    wa
    wb
    wph
    @36
    cA
    cV
    wcel
    @51
    gsumpt.f
    gsumpt.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    @45
    cF
    cvv
    cvv
    c.0
    isfsupp
    syl2anc
    mpbir2and
    gsumzres
    wph
    @18
    cX
    cA
    wcel
    @21
    @5
    @6
    wceq
    gsumpt.g
    gsumpt.x
    @25
    @3
    cB
    @6
    va
    cG
    cX
    cA
    gsumpt.b
    @2
    cX
    cF
    fveq2
    gsumsn
    syl3anc
    3eqtr3d
end
