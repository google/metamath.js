include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "cv.mm"
include "cle.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "cneg.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "renegcl.mm"
include "rexrd.mm"
include "ad2antlr.mm"
include "cvv.mm"
include "wf.mm"
include "reex.mm"
include "ssexd.mm"
include "fex.mm"
include "syl2anc.mm"
include "limsupcl.mm"
include "syl.mm"
include "ad2antrr.mm"
include "mnfltd.mm"
include "wss.mm"
include "ressxr.mm"
include "fssd.mm"
include "csup.mm"
include "wceq.mm"
include "simpr.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "w3a.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simp13.mm"
include "simp2.mm"
include "simp3.mm"
include "rspa.mm"
include "imp.mm"
include "syl21anc.mm"
include "simp11l.mm"
include "ffvelrnda.mm"
include "simp11r.mm"
include "absled.mm"
include "mpbid.mm"
include "simpld.mm"
include "3exp.mm"
include "ralrimi.mm"
include "adantr.mm"
include "reximdai.mm"
include "mpd.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvrexv.mm"
include "sylibr.mm"
include "limsupbnd2.mm"
include "xrltletrd.mm"
include "r19.29a.mm"
include "rexr.mm"
include "pnfxr.mm"
include "simprd.mm"
include "breq1d.mm"
include "limsupbnd1.mm"
include "ltpnf.mm"
include "xrlelttrd.mm"
include "wb.mm"
include "xrrebnd.mm"
include "mpbir2and.mm"

theorem limsupre
  let wph: wff ph
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vb: setvar b
  let vh: setvar h
  let vi: setvar i
  assume limsupre.1: |- ( ph -> B C_ RR )
  assume limsupre.2: |- ( ph -> sup ( B , RR* , < ) = +oo )
  assume limsupre.f: |- ( ph -> F : B --> RR )
  assume limsupre.bnd: |- ( ph -> E. b e. RR E. k e. RR A. j e. B ( k <_ j -> ( abs ` ( F ` j ) ) <_ b ) )

  disjoint B j
  disjoint B k
  disjoint j k
  disjoint F b
  disjoint F j
  disjoint F k
  disjoint b j
  disjoint b k
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint B h
  disjoint B i
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint i j
  disjoint i k
  disjoint F h
  disjoint F i
  disjoint b h
  disjoint b i
  disjoint h ph
  disjoint i ph
  assert |- ( ph -> ( limsup ` F ) e. RR )

  proof
    wph
    cF
    clsp
    cfv
    #
    cr
    wcel
    #
    cmnf
    @0
    clt
    wbr
    #
    @0
    cpnf
    clt
    wbr
    #
    wph
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    @5
    cF
    cfv
    #
    cabs
    cfv
    vb
    cv
    #
    cle
    wbr
    #
    wi
    #
    vj
    cB
    wral
    #
    vk
    cr
    wrex
    #
    @2
    vb
    cr
    wph
    @8
    cr
    wcel
    #
    wa
    #
    @12
    wa
    #
    cmnf
    @8
    cneg
    #
    @0
    cmnf
    cxr
    wcel
    @15
    mnfxr
    a1i
    @13
    @16
    cxr
    wcel
    wph
    @12
    @13
    @16
    @8
    renegcl
    #
    rexrd
    ad2antlr
    #
    wph
    @0
    cxr
    wcel
    #
    @13
    @12
    wph
    cF
    cvv
    wcel
    #
    @19
    wph
    cB
    cr
    cF
    wf
    cB
    cvv
    wcel
    @20
    limsupre.f
    wph
    cB
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    limsupre.1
    ssexd
    cB
    cr
    cvv
    cF
    fex
    syl2anc
    cF
    cvv
    limsupcl
    syl
    #
    ad2antrr
    #
    @13
    cmnf
    @16
    clt
    wbr
    wph
    @12
    @13
    @16
    @17
    mnfltd
    ad2antlr
    @15
    @16
    cB
    vi
    vh
    cF
    wph
    cB
    cr
    wss
    @13
    @12
    limsupre.1
    ad2antrr
    #
    wph
    cB
    cxr
    cF
    wf
    @13
    @12
    wph
    cB
    cr
    cxr
    cF
    limsupre.f
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    fssd
    ad2antrr
    #
    @18
    wph
    cB
    cxr
    clt
    csup
    cpnf
    wceq
    @13
    @12
    limsupre.2
    ad2antrr
    @15
    @6
    @16
    @7
    cle
    wbr
    #
    wi
    #
    vj
    cB
    wral
    #
    vk
    cr
    wrex
    #
    vh
    cv
    #
    vi
    cv
    #
    cle
    wbr
    #
    @16
    @30
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vi
    cB
    wral
    #
    vh
    cr
    wrex
    @15
    @12
    @28
    @14
    @12
    simpr
    #
    @15
    @11
    @27
    vk
    cr
    @14
    @12
    vk
    @14
    vk
    nfv
    @11
    vk
    cr
    nfre1
    nfan
    #
    @14
    @4
    cr
    wcel
    #
    @11
    @27
    wi
    wi
    @12
    @14
    @38
    @11
    @27
    @14
    @38
    @11
    w3a
    #
    @26
    vj
    cB
    @14
    @38
    @11
    vj
    @14
    vj
    nfv
    @38
    vj
    nfv
    @10
    vj
    cB
    nfra1
    nf3an
    #
    @39
    @5
    cB
    wcel
    #
    @6
    @25
    @39
    @41
    @6
    w3a
    #
    @25
    @7
    @8
    cle
    wbr
    #
    @42
    @9
    @25
    @43
    wa
    @42
    @11
    @41
    @6
    @9
    @14
    @38
    @11
    @41
    @6
    simp13
    @39
    @41
    @6
    simp2
    #
    @39
    @41
    @6
    simp3
    @11
    @41
    wa
    @6
    @9
    @10
    vj
    cB
    rspa
    imp
    syl21anc
    @42
    @7
    @8
    @42
    wph
    @41
    @7
    cr
    wcel
    wph
    @13
    @38
    @11
    @41
    @6
    simp11l
    @44
    wph
    cB
    cr
    @5
    cF
    limsupre.f
    ffvelrnda
    syl2anc
    wph
    @13
    @38
    @11
    @41
    @6
    simp11r
    absled
    mpbid
    #
    simpld
    3exp
    ralrimi
    3exp
    adantr
    reximdai
    mpd
    @35
    @27
    vh
    vk
    cr
    @35
    @29
    @5
    cle
    wbr
    #
    @25
    wi
    #
    vj
    cB
    wral
    @29
    @4
    wceq
    #
    @27
    @34
    @47
    vi
    vj
    cB
    @30
    @5
    wceq
    #
    @31
    @46
    @33
    @25
    @30
    @5
    @29
    cle
    breq2
    #
    @49
    @32
    @7
    @16
    cle
    @30
    @5
    cF
    fveq2
    #
    breq2d
    imbi12d
    cbvralv
    @48
    @47
    @26
    vj
    cB
    @48
    @46
    @6
    @25
    @29
    @4
    @5
    cle
    breq1
    #
    imbi1d
    ralbidv
    syl5bb
    cbvrexv
    sylibr
    limsupbnd2
    xrltletrd
    limsupre.bnd
    r19.29a
    wph
    @12
    @3
    vb
    cr
    @15
    @0
    @8
    cpnf
    @22
    @13
    @8
    cxr
    wcel
    wph
    @12
    @8
    rexr
    ad2antlr
    #
    cpnf
    cxr
    wcel
    @15
    pnfxr
    a1i
    @15
    @8
    cB
    vi
    vh
    cF
    @23
    @24
    @53
    @15
    @6
    @43
    wi
    #
    vj
    cB
    wral
    #
    vk
    cr
    wrex
    #
    @31
    @32
    @8
    cle
    wbr
    #
    wi
    #
    vi
    cB
    wral
    #
    vh
    cr
    wrex
    @15
    @12
    @56
    @36
    @15
    @11
    @55
    vk
    cr
    @37
    @14
    @38
    @11
    @55
    wi
    wi
    @12
    @14
    @38
    @11
    @55
    @39
    @54
    vj
    cB
    @40
    @39
    @41
    @6
    @43
    @42
    @25
    @43
    @45
    simprd
    3exp
    ralrimi
    3exp
    adantr
    reximdai
    mpd
    @59
    @55
    vh
    vk
    cr
    @59
    @46
    @43
    wi
    #
    vj
    cB
    wral
    @48
    @55
    @58
    @60
    vi
    vj
    cB
    @49
    @31
    @46
    @57
    @43
    @50
    @49
    @32
    @7
    @8
    cle
    @51
    breq1d
    imbi12d
    cbvralv
    @48
    @60
    @54
    vj
    cB
    @48
    @46
    @6
    @43
    @52
    imbi1d
    ralbidv
    syl5bb
    cbvrexv
    sylibr
    limsupbnd1
    @13
    @8
    cpnf
    clt
    wbr
    wph
    @12
    @8
    ltpnf
    ad2antlr
    xrlelttrd
    limsupre.bnd
    r19.29a
    wph
    @19
    @1
    @2
    @3
    wa
    wb
    @21
    @0
    xrrebnd
    syl
    mpbir2and
end
