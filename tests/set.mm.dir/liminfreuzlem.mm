include "clsi.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cneg.mm"
include "cmpt.mm"
include "clsp.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cxne.mm"
include "nfv.mm"
include "liminfvaluz4.mm"
include "eleq1d.mm"
include "cxr.mm"
include "cvv.mm"
include "fvexi.mm"
include "mptex.mm"
include "limsupcl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "xnegred.mm"
include "bitr4d.mm"
include "ffvelrnda.mm"
include "renegcld.mm"
include "limsupreuzmpt.mm"
include "renegcl.mm"
include "ad2antlr.mm"
include "simpllr.mm"
include "wf.mm"
include "ad2antrr.mm"
include "uztrn2.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "adantllr.mm"
include "leneg2d.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "imp.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdva2.mm"
include "lenegd.mm"
include "breq1.mm"
include "impbid.mm"
include "adantlr.mm"
include "simplr.mm"
include "leneg3d.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem liminfreuzlem
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume liminfreuzlem.1: |- F/_ j F
  assume liminfreuzlem.2: |- ( ph -> M e. ZZ )
  assume liminfreuzlem.3: |- Z = ( ZZ>= ` M )
  assume liminfreuzlem.4: |- ( ph -> F : Z --> RR )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint F y
  disjoint k y
  disjoint x y
  disjoint Z y
  disjoint j y
  disjoint ph y
  assert |- ( ph -> ( ( liminf ` F ) e. RR <-> ( E. x e. RR A. k e. Z E. j e. ( ZZ>= ` k ) ( F ` j ) <_ x /\ E. x e. RR A. j e. Z x <_ ( F ` j ) ) ) )

  proof
    wph
    cF
    clsi
    cfv
    #
    cr
    wcel
    #
    vj
    cZ
    vj
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    clsp
    cfv
    #
    cr
    wcel
    #
    @3
    vx
    cv
    #
    cle
    wbr
    #
    vj
    vk
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @8
    @3
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    wa
    #
    wph
    @1
    @6
    cxne
    #
    cr
    wcel
    @7
    wph
    @0
    @19
    cr
    wph
    vj
    cF
    cM
    cZ
    wph
    vj
    nfv
    #
    liminfreuzlem.1
    liminfreuzlem.2
    liminfreuzlem.3
    liminfreuzlem.4
    liminfvaluz4
    eleq1d
    wph
    @6
    @6
    cxr
    wcel
    #
    wph
    @5
    cvv
    wcel
    @21
    vj
    cZ
    @4
    cZ
    cM
    cuz
    liminfreuzlem.3
    fvexi
    mptex
    @5
    cvv
    limsupcl
    ax-mp
    a1i
    xnegred
    bitr4d
    wph
    @7
    vy
    cv
    #
    @4
    cle
    wbr
    #
    vj
    @11
    wrex
    #
    vk
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @4
    @22
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    wa
    @18
    wph
    vy
    @4
    vj
    vk
    cM
    cZ
    @20
    liminfreuzlem.2
    liminfreuzlem.3
    wph
    @2
    cZ
    wcel
    #
    wa
    @3
    wph
    cZ
    cr
    @2
    cF
    liminfreuzlem.4
    ffvelrnda
    #
    renegcld
    limsupreuzmpt
    wph
    @26
    @14
    @29
    @17
    wph
    @26
    @14
    wph
    @25
    @14
    vy
    cr
    wph
    @22
    cr
    wcel
    #
    wa
    #
    @25
    wa
    @22
    cneg
    #
    cr
    wcel
    #
    @3
    @34
    cle
    wbr
    #
    vj
    @11
    wrex
    #
    vk
    cZ
    wral
    #
    @14
    @32
    @35
    wph
    @25
    @22
    renegcl
    #
    ad2antlr
    @33
    @25
    @38
    @33
    @25
    @38
    @33
    @24
    @37
    vk
    cZ
    @33
    @10
    cZ
    wcel
    #
    wa
    #
    @23
    @36
    vj
    @11
    @41
    @2
    @11
    wcel
    #
    wa
    @22
    @3
    wph
    @32
    @40
    @42
    simpllr
    wph
    @40
    @42
    @3
    cr
    wcel
    #
    @32
    wph
    @40
    wa
    @42
    wa
    cZ
    cr
    @2
    cF
    wph
    cZ
    cr
    cF
    wf
    @40
    @42
    liminfreuzlem.4
    ad2antrr
    @40
    @42
    @30
    wph
    cM
    @2
    @10
    cZ
    liminfreuzlem.3
    uztrn2
    adantll
    ffvelrnd
    #
    adantllr
    leneg2d
    rexbidva
    ralbidva
    biimpd
    imp
    @13
    @38
    vx
    @34
    cr
    @8
    @34
    wceq
    #
    @12
    @37
    vk
    cZ
    @45
    @9
    @36
    vj
    @11
    @8
    @34
    @3
    cle
    breq2
    rexbidv
    ralbidv
    rspcev
    syl2anc
    rexlimdva2
    wph
    @13
    @26
    vx
    cr
    wph
    @8
    cr
    wcel
    #
    wa
    #
    @13
    wa
    @8
    cneg
    #
    cr
    wcel
    #
    @48
    @4
    cle
    wbr
    #
    vj
    @11
    wrex
    #
    vk
    cZ
    wral
    #
    @26
    @46
    @49
    wph
    @13
    @8
    renegcl
    #
    ad2antlr
    @47
    @13
    @52
    @47
    @13
    @52
    @47
    @12
    @51
    vk
    cZ
    @47
    @40
    wa
    #
    @9
    @50
    vj
    @11
    @54
    @42
    wa
    @3
    @8
    wph
    @40
    @42
    @43
    @46
    @44
    adantllr
    wph
    @46
    @40
    @42
    simpllr
    lenegd
    rexbidva
    ralbidva
    biimpd
    imp
    @25
    @52
    vy
    @48
    cr
    @22
    @48
    wceq
    #
    @24
    @51
    vk
    cZ
    @55
    @23
    @50
    vj
    @11
    @22
    @48
    @4
    cle
    breq1
    rexbidv
    ralbidv
    rspcev
    syl2anc
    rexlimdva2
    impbid
    wph
    @29
    @17
    wph
    @28
    @17
    vy
    cr
    @33
    @28
    wa
    @35
    @34
    @3
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    @17
    @32
    @35
    wph
    @28
    @39
    ad2antlr
    @33
    @28
    @57
    @33
    @28
    @57
    @33
    @27
    @56
    vj
    cZ
    @33
    @30
    wa
    @3
    @22
    wph
    @30
    @43
    @32
    @31
    adantlr
    wph
    @32
    @30
    simplr
    leneg3d
    ralbidva
    biimpd
    imp
    @16
    @57
    vx
    @34
    cr
    @45
    @15
    @56
    vj
    cZ
    @8
    @34
    @3
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    rexlimdva2
    wph
    @16
    @29
    vx
    cr
    @47
    @16
    wa
    @49
    @4
    @48
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    @29
    @46
    @49
    wph
    @16
    @53
    ad2antlr
    @47
    @16
    @59
    @47
    @16
    @59
    @47
    @15
    @58
    vj
    cZ
    @47
    @30
    wa
    @8
    @3
    wph
    @46
    @30
    simplr
    wph
    @30
    @43
    @46
    @31
    adantlr
    lenegd
    ralbidva
    biimpd
    imp
    @28
    @59
    vy
    @48
    cr
    @55
    @27
    @58
    vj
    cZ
    @22
    @48
    @4
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    rexlimdva2
    impbid
    anbi12d
    bitrd
    bitrd
end
