include "cpnf.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "clt.mm"
include "cr.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wa.mm"
include "c1.mm"
include "ctopon.mm"
include "cle.mm"
include "cordt.mm"
include "crest.mm"
include "cxrs.mm"
include "cress.mm"
include "ctopn.mm"
include "eqid.mm"
include "xrstopn.mm"
include "resstopn.mm"
include "eqtr4i.mm"
include "cxr.mm"
include "wss.mm"
include "letopon.mm"
include "iccssxr.mm"
include "resttopon.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "a1i.mm"
include "nnuz.mm"
include "1zzd.mm"
include "lmbrf.mm"
include "0xr.mm"
include "pnfxr.mm"
include "0lepnf.mm"
include "ubicc2.mm"
include "mp3an.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "cioc.mm"
include "cin.mm"
include "rexr.mm"
include "ltpnf.mm"
include "ubioc1.mm"
include "syl3anc.mm"
include "0ltpnf.mm"
include "jctir.mm"
include "elin.mm"
include "sylibr.mm"
include "ad2antlr.mm"
include "ctop.mm"
include "cvv.mm"
include "letop.mm"
include "ovex.mm"
include "iocpnfordt.mm"
include "inopn.mm"
include "elrestr.mm"
include "wceq.mm"
include "inss2.mm"
include "iocssicc.mm"
include "sstri.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "incom.mm"
include "eqtr3i.mm"
include "3eltr4i.mm"
include "wb.mm"
include "eleq2.mm"
include "adantl.mm"
include "biimprd.mm"
include "simp-5r.mm"
include "rexrd.mm"
include "simpr.mm"
include "simp-4r.mm"
include "eleqtrd.mm"
include "simplbi.mm"
include "syl.mm"
include "w3a.mm"
include "elioc1.mm"
include "mpan2.mm"
include "biimpa.mm"
include "simp2d.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "syl6ibr.mm"
include "imim12d.mm"
include "rspcimdv.mm"
include "imp.mm"
include "mpd.mm"
include "ralrimdva.mm"
include "simplll.mm"
include "simpllr.mm"
include "pnfneige0.mm"
include "simplr.mm"
include "r19.29r.mm"
include "simp-4l.mm"
include "uznnssnn.mm"
include "sseldd.mm"
include "jca.mm"
include "ffvelrnda.mm"
include "eqeltrrd.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "pnfge.mm"
include "biimpar.mm"
include "syl13anc.mm"
include "adantlr.mm"
include "syl21anc.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "syl12anc.mm"
include "exp31.mm"
include "impbid.mm"
include "bitrd.mm"

theorem lmxrge0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let va: setvar a
  let vl: setvar l
  assume lmxrge0.j: |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
  assume lmxrge0.6: |- ( ph -> F : NN --> ( 0 [,] +oo ) )
  assume lmxrge0.7: |- ( ( ph /\ k e. NN ) -> ( F ` k ) = A )

  disjoint j x
  disjoint A j
  disjoint A x
  disjoint j k
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint J k
  disjoint J x
  disjoint k ph
  disjoint ph x
  disjoint a j
  disjoint a l
  disjoint a x
  disjoint A a
  disjoint j l
  disjoint l x
  disjoint A l
  disjoint a k
  disjoint F a
  disjoint k l
  disjoint F l
  disjoint J a
  disjoint J l
  disjoint a ph
  disjoint l ph
  assert |- ( ph -> ( F ( ~~>t ` J ) +oo <-> A. x e. RR E. j e. NN A. k e. ( ZZ>= ` j ) x < A ) )

  proof
    wph
    cF
    cpnf
    cJ
    clm
    cfv
    wbr
    #
    cpnf
    va
    cv
    #
    wcel
    #
    cA
    @1
    wcel
    #
    vk
    vl
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vl
    cn
    wrex
    #
    wi
    #
    va
    cJ
    wral
    #
    vx
    cv
    #
    cA
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    cr
    wral
    #
    wph
    @0
    cpnf
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @9
    wa
    @9
    wph
    va
    cA
    cpnf
    vl
    vk
    cF
    cJ
    c1
    @17
    cn
    cJ
    @17
    ctopon
    cfv
    #
    wcel
    wph
    cJ
    cle
    cordt
    cfv
    #
    @17
    crest
    co
    #
    @19
    cJ
    cxrs
    @17
    cress
    co
    #
    ctopn
    cfv
    @21
    lmxrge0.j
    @17
    @22
    @20
    cxrs
    @22
    eqid
    xrstopn
    resstopn
    eqtr4i
    #
    @20
    cxr
    ctopon
    cfv
    wcel
    @17
    cxr
    wss
    @21
    @19
    wcel
    letopon
    cc0
    cpnf
    iccssxr
    #
    @17
    @20
    cxr
    resttopon
    mp2an
    eqeltri
    a1i
    nnuz
    wph
    1zzd
    lmxrge0.6
    lmxrge0.7
    lmbrf
    @18
    @9
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cc0
    cpnf
    cle
    wbr
    @18
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    ubicc2
    mp3an
    biantrur
    syl6bbr
    wph
    @9
    @16
    wph
    @9
    @15
    vx
    cr
    wph
    @10
    cr
    wcel
    #
    wa
    #
    @9
    @15
    @28
    @9
    wa
    cpnf
    @10
    cpnf
    cioc
    co
    #
    cc0
    cpnf
    cioc
    co
    #
    cin
    #
    wcel
    #
    @15
    @27
    @32
    wph
    @9
    @27
    cpnf
    @29
    wcel
    #
    cpnf
    @30
    wcel
    #
    wa
    @32
    @27
    @33
    @34
    @27
    @10
    cxr
    wcel
    #
    @26
    @10
    cpnf
    clt
    wbr
    @33
    @10
    rexr
    @26
    @27
    pnfxr
    a1i
    @10
    ltpnf
    @10
    cpnf
    ubioc1
    syl3anc
    @25
    @26
    cc0
    cpnf
    clt
    wbr
    @34
    0xr
    pnfxr
    0ltpnf
    cc0
    cpnf
    ubioc1
    mp3an
    jctir
    cpnf
    @29
    @30
    elin
    sylibr
    ad2antlr
    @28
    @9
    @32
    @15
    wi
    #
    @28
    @8
    @36
    va
    @31
    cJ
    @31
    cJ
    wcel
    @28
    @31
    @17
    cin
    #
    @21
    @31
    cJ
    @20
    ctop
    wcel
    #
    @17
    cvv
    wcel
    @31
    @20
    wcel
    #
    @37
    @21
    wcel
    letop
    cc0
    cpnf
    cicc
    ovex
    @38
    @29
    @20
    wcel
    @30
    @20
    wcel
    @39
    letop
    @10
    iocpnfordt
    cc0
    iocpnfordt
    @29
    @30
    @20
    inopn
    mp3an
    @31
    @17
    @20
    ctop
    cvv
    elrestr
    mp3an
    @17
    @31
    cin
    #
    @31
    @37
    @31
    @17
    wss
    @40
    @31
    wceq
    @31
    @30
    @17
    @29
    @30
    inss2
    cc0
    cpnf
    iocssicc
    sstri
    @31
    @17
    sseqin2
    mpbi
    @17
    @31
    incom
    eqtr3i
    @23
    3eltr4i
    a1i
    @28
    @1
    @31
    wceq
    #
    wa
    #
    @32
    @2
    @7
    @15
    @42
    @2
    @32
    @41
    @2
    @32
    wb
    @28
    @1
    @31
    cpnf
    eleq2
    adantl
    biimprd
    @42
    @7
    @11
    vk
    @5
    wral
    #
    vl
    cn
    wrex
    #
    @15
    @42
    @6
    @43
    vl
    cn
    @42
    @4
    cn
    wcel
    #
    wa
    #
    @3
    @11
    vk
    @5
    @46
    vk
    cv
    #
    @5
    wcel
    #
    wa
    #
    @3
    @11
    @49
    @3
    wa
    #
    @35
    cA
    @29
    wcel
    #
    @11
    @50
    @10
    wph
    @27
    @41
    @45
    @48
    @3
    simp-5r
    rexrd
    @50
    cA
    @31
    wcel
    #
    @51
    @50
    cA
    @1
    @31
    @49
    @3
    simpr
    @28
    @41
    @45
    @48
    @3
    simp-4r
    eleqtrd
    @52
    @51
    cA
    @30
    wcel
    cA
    @29
    @30
    elin
    simplbi
    syl
    @35
    @51
    wa
    cA
    cxr
    wcel
    #
    @11
    cA
    cpnf
    cle
    wbr
    #
    @35
    @51
    @53
    @11
    @54
    w3a
    #
    @35
    @26
    @51
    @55
    wb
    pnfxr
    @10
    cpnf
    cA
    elioc1
    mpan2
    #
    biimpa
    simp2d
    syl2anc
    ex
    ralimdva
    reximdva
    @14
    @43
    vj
    vl
    cn
    @12
    @4
    wceq
    @11
    vk
    @13
    @5
    @12
    @4
    cuz
    fveq2
    raleqdv
    cbvrexv
    #
    syl6ibr
    imim12d
    rspcimdv
    imp
    mpd
    ex
    ralrimdva
    wph
    @16
    @8
    va
    cJ
    wph
    @1
    cJ
    wcel
    #
    wa
    #
    @16
    @2
    @7
    @59
    @16
    wa
    #
    @2
    wa
    #
    wph
    @29
    @1
    wss
    #
    vx
    cr
    wrex
    #
    @16
    @7
    wph
    @58
    @16
    @2
    simplll
    @61
    @58
    @2
    @63
    wph
    @58
    @16
    @2
    simpllr
    @60
    @2
    simpr
    vx
    @1
    cJ
    lmxrge0.j
    pnfneige0
    syl2anc
    @59
    @16
    @2
    simplr
    wph
    @63
    @16
    wa
    #
    @7
    @64
    @62
    @15
    wa
    #
    vx
    cr
    wrex
    wph
    @7
    @62
    @15
    vx
    cr
    r19.29r
    wph
    @65
    @7
    vx
    cr
    @28
    @62
    @15
    @7
    @15
    @44
    @28
    @62
    wa
    #
    @7
    @57
    @66
    @43
    @6
    vl
    cn
    @66
    @45
    wa
    #
    @11
    @3
    vk
    @5
    @67
    @48
    wa
    #
    wph
    @47
    cn
    wcel
    #
    wa
    #
    @27
    @62
    @11
    @3
    wi
    @68
    wph
    @69
    wph
    @27
    @62
    @45
    @48
    simp-4l
    @68
    @5
    cn
    @47
    @45
    @5
    cn
    wss
    @66
    @48
    @4
    uznnssnn
    ad2antlr
    @67
    @48
    simpr
    sseldd
    jca
    wph
    @27
    @62
    @45
    @48
    simp-4r
    @28
    @62
    @45
    @48
    simpllr
    @70
    @27
    wa
    #
    @62
    wa
    #
    @11
    @3
    @72
    @11
    wa
    @29
    @1
    cA
    @71
    @62
    @11
    simplr
    @71
    @11
    @51
    @62
    @71
    @11
    wa
    #
    @35
    @53
    @11
    @54
    @51
    @73
    @10
    @70
    @27
    @11
    simplr
    rexrd
    @70
    @53
    @27
    @11
    @70
    @17
    cxr
    cA
    @24
    @70
    @47
    cF
    cfv
    cA
    @17
    lmxrge0.7
    wph
    cn
    @17
    @47
    cF
    lmxrge0.6
    ffvelrnda
    eqeltrrd
    sseldi
    ad2antrr
    #
    @71
    @11
    simpr
    @73
    @53
    @54
    @74
    cA
    pnfge
    syl
    @35
    @51
    @55
    @56
    biimpar
    syl13anc
    adantlr
    sseldd
    ex
    syl21anc
    ralimdva
    reximdva
    syl5bi
    expimpd
    rexlimdva
    syl5
    imp
    syl12anc
    exp31
    ralrimdva
    impbid
    bitrd
end
