include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "raleqbi1dv.mm"
include "imbi2d.mm"
include "ral0.mm"
include "a1i.mm"
include "w3a.mm"
include "ccnv.mm"
include "wn.mm"
include "wf.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "adantl.mm"
include "infpssrlem3.mm"
include "ffvelrnda.mm"
include "ancoms.mm"
include "ffvelrnd.mm"
include "eldifbd.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "infpssrlem2.mm"
include "adantr.mm"
include "infpssrlem1.mm"
include "3netr4d.mm"
include "3adant3.mm"
include "neeq2d.mm"
include "syl5ibr.mm"
include "adantrd.mm"
include "wrex.mm"
include "simpr.mm"
include "peano2.mm"
include "elnn.mm"
include "3ad2antl1.mm"
include "simpl.mm"
include "nnsuc.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfan.mm"
include "simpl3.mm"
include "word.mm"
include "wb.mm"
include "nnord.mm"
include "ordsucelsuc.mm"
include "syl.mm"
include "mpbird.mm"
include "adantrr.mm"
include "rsp.mm"
include "sylc.mm"
include "wf1.mm"
include "f1of1.mm"
include "ad2antlr.mm"
include "adantll.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "necon3bid.mm"
include "biimprd.mm"
include "neeq12d.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "adantrl.mm"
include "3adantl3.mm"
include "mpd.mm"
include "expr.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "com3l.mm"
include "rexlimd.mm"
include "ex.mm"
include "pm2.61ine.mm"
include "ralrimiva.mm"
include "cbvralv.mm"
include "sylib.mm"
include "3exp.mm"
include "a2d.mm"
include "finds.mm"
include "impcom.mm"
include "rspccv.mm"
include "3impia.mm"

theorem infpssrlem4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume infpssrlem.a: |- ( ph -> B C_ A )
  assume infpssrlem.c: |- ( ph -> F : B -1-1-onto-> A )
  assume infpssrlem.d: |- ( ph -> C e. ( A \ B ) )
  assume infpssrlem.e: |- G = ( rec ( `' F , C ) |` _om )


  assert |- ( ( ph /\ M e. _om /\ N e. M ) -> ( G ` M ) =/= ( G ` N ) )

  proof
    wph
    cM
    com
    wcel
    #
    cN
    cM
    wcel
    #
    cM
    cG
    cfv
    #
    cN
    cG
    cfv
    #
    wne
    #
    wph
    @0
    wa
    @2
    vb
    cv
    #
    cG
    cfv
    #
    wne
    #
    vb
    cM
    wral
    #
    @1
    @4
    wi
    @0
    wph
    @8
    wph
    vc
    cv
    #
    cG
    cfv
    #
    @6
    wne
    #
    vb
    @9
    wral
    #
    wi
    wph
    c0
    cG
    cfv
    #
    @6
    wne
    #
    vb
    c0
    wral
    #
    wi
    wph
    vd
    cv
    #
    cG
    cfv
    #
    @6
    wne
    #
    vb
    @16
    wral
    #
    wi
    wph
    @16
    csuc
    #
    cG
    cfv
    #
    @6
    wne
    #
    vb
    @20
    wral
    #
    wi
    wph
    @8
    wi
    vc
    vd
    cM
    @9
    c0
    wceq
    #
    @12
    @15
    wph
    @11
    @14
    vb
    @9
    c0
    @24
    @10
    @13
    @6
    @9
    c0
    cG
    fveq2
    #
    neeq1d
    raleqbi1dv
    imbi2d
    @9
    @16
    wceq
    #
    @12
    @19
    wph
    @11
    @18
    vb
    @9
    @16
    @26
    @10
    @17
    @6
    @9
    @16
    cG
    fveq2
    neeq1d
    raleqbi1dv
    imbi2d
    @9
    @20
    wceq
    #
    @12
    @23
    wph
    @11
    @22
    vb
    @9
    @20
    @27
    @10
    @21
    @6
    @9
    @20
    cG
    fveq2
    neeq1d
    raleqbi1dv
    imbi2d
    @9
    cM
    wceq
    #
    @12
    @8
    wph
    @11
    @7
    vb
    @9
    cM
    @28
    @10
    @2
    @6
    @9
    cM
    cG
    fveq2
    neeq1d
    raleqbi1dv
    imbi2d
    @15
    wph
    @14
    vb
    ral0
    a1i
    @16
    com
    wcel
    #
    wph
    @19
    @23
    @29
    wph
    @19
    @23
    @29
    wph
    @19
    w3a
    #
    @21
    @10
    wne
    #
    vc
    @20
    wral
    @23
    @30
    @31
    vc
    @20
    @30
    @9
    @20
    wcel
    #
    wa
    #
    @31
    wi
    @9
    c0
    @24
    @30
    @31
    @32
    @30
    @31
    @24
    @21
    @13
    wne
    #
    @29
    wph
    @34
    @19
    @29
    wph
    wa
    #
    @17
    cF
    ccnv
    #
    cfv
    #
    cC
    @21
    @13
    @35
    @37
    cB
    wcel
    cC
    cB
    wcel
    wn
    #
    @37
    cC
    wne
    @35
    cA
    cB
    @17
    @36
    wph
    cA
    cB
    @36
    wf
    #
    @29
    wph
    cB
    cA
    cF
    wf1o
    #
    cA
    cB
    @36
    wf1o
    #
    @39
    infpssrlem.c
    cB
    cA
    cF
    f1ocnv
    #
    cA
    cB
    @36
    f1of
    3syl
    adantl
    wph
    @29
    @17
    cA
    wcel
    #
    wph
    com
    cA
    @16
    cG
    wph
    cA
    cB
    cC
    cF
    cG
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem3
    #
    ffvelrnda
    ancoms
    #
    ffvelrnd
    wph
    @38
    @29
    wph
    cC
    cA
    cB
    infpssrlem.d
    eldifbd
    adantl
    @37
    cC
    cB
    nelne2
    syl2anc
    @29
    @21
    @37
    wceq
    #
    wph
    wph
    cA
    cB
    cC
    cF
    cG
    @16
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem2
    #
    adantr
    wph
    @13
    cC
    wceq
    @29
    wph
    cA
    cB
    cC
    cF
    cG
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem1
    adantl
    3netr4d
    3adant3
    @24
    @10
    @13
    @21
    @25
    neeq2d
    syl5ibr
    adantrd
    @9
    c0
    wne
    #
    @33
    @31
    @48
    @33
    wa
    #
    @9
    @5
    csuc
    #
    wceq
    #
    vb
    com
    wrex
    #
    @31
    @49
    @9
    com
    wcel
    #
    @48
    @52
    @33
    @53
    @48
    @29
    wph
    @32
    @53
    @19
    @29
    @32
    wa
    @32
    @20
    com
    wcel
    #
    @53
    @29
    @32
    simpr
    @29
    @54
    @32
    @16
    peano2
    adantr
    @9
    @20
    elnn
    syl2anc
    3ad2antl1
    adantl
    @48
    @33
    simpl
    vb
    @9
    nnsuc
    syl2anc
    @33
    @52
    @31
    wi
    @48
    @33
    @51
    @31
    vb
    com
    @30
    @32
    vb
    @29
    wph
    @19
    vb
    @29
    vb
    nfv
    wph
    vb
    nfv
    @18
    vb
    @16
    nfra1
    nf3an
    @32
    vb
    nfv
    nfan
    @31
    vb
    nfv
    @51
    @33
    @5
    com
    wcel
    #
    @31
    @51
    @33
    @55
    @31
    wi
    #
    wi
    @30
    @50
    @20
    wcel
    #
    wa
    #
    @55
    @21
    @50
    cG
    cfv
    #
    wne
    #
    wi
    #
    wi
    @30
    @57
    @55
    @60
    @30
    @57
    @55
    wa
    #
    wa
    #
    @18
    @60
    @63
    @19
    @5
    @16
    wcel
    #
    @18
    @29
    wph
    @19
    @62
    simpl3
    @30
    @57
    @64
    @55
    @29
    wph
    @57
    @64
    @19
    @29
    @57
    wa
    #
    @64
    @57
    @29
    @57
    simpr
    @65
    @16
    word
    #
    @64
    @57
    wb
    @29
    @66
    @57
    @16
    nnord
    adantr
    @5
    @16
    ordsucelsuc
    syl
    mpbird
    3ad2antl1
    adantrr
    @18
    vb
    @16
    rsp
    sylc
    @29
    wph
    @62
    @18
    @60
    wi
    #
    @19
    @35
    @55
    @67
    @57
    @35
    @55
    wa
    #
    @18
    @37
    @6
    @36
    cfv
    #
    wne
    #
    @60
    @68
    @70
    @18
    @68
    @37
    @69
    @17
    @6
    @68
    cA
    cB
    @36
    wf1
    #
    @43
    @6
    cA
    wcel
    #
    @37
    @69
    wceq
    @17
    @6
    wceq
    wb
    wph
    @71
    @29
    @55
    wph
    @40
    @41
    @71
    infpssrlem.c
    @42
    cA
    cB
    @36
    f1of1
    3syl
    ad2antlr
    @35
    @43
    @55
    @45
    adantr
    wph
    @55
    @72
    @29
    wph
    com
    cA
    @5
    cG
    @44
    ffvelrnda
    adantll
    cA
    cB
    @17
    @6
    @36
    f1fveq
    syl12anc
    necon3bid
    biimprd
    @29
    @55
    @60
    @70
    wb
    wph
    @29
    @55
    wa
    @21
    @37
    @59
    @69
    @29
    @46
    @55
    @47
    adantr
    @55
    @59
    @69
    wceq
    @29
    wph
    cA
    cB
    cC
    cF
    cG
    @5
    infpssrlem.a
    infpssrlem.c
    infpssrlem.d
    infpssrlem.e
    infpssrlem2
    adantl
    neeq12d
    adantlr
    sylibrd
    adantrl
    3adantl3
    mpd
    expr
    @51
    @33
    @58
    @56
    @61
    @51
    @32
    @57
    @30
    @9
    @50
    @20
    eleq1
    anbi2d
    @51
    @31
    @60
    @55
    @51
    @10
    @59
    @21
    @9
    @50
    cG
    fveq2
    neeq2d
    imbi2d
    imbi12d
    mpbiri
    com3l
    rexlimd
    adantl
    mpd
    ex
    pm2.61ine
    ralrimiva
    @31
    @22
    vc
    vb
    @20
    @9
    @5
    wceq
    @10
    @6
    @21
    @9
    @5
    cG
    fveq2
    neeq2d
    cbvralv
    sylib
    3exp
    a2d
    finds
    impcom
    @7
    @4
    vb
    cN
    cM
    @5
    cN
    wceq
    @6
    @3
    @2
    @5
    cN
    cG
    fveq2
    neeq2d
    rspccv
    syl
    3impia
end
