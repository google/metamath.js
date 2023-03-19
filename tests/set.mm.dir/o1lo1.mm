include "cmpt.mm"
include "cdm.mm"
include "cr.mm"
include "wss.mm"
include "co1.mm"
include "wcel.mm"
include "clo1.mm"
include "cneg.mm"
include "wa.mm"
include "wi.mm"
include "o1dm.mm"
include "a1i.mm"
include "lo1dm.mm"
include "adantr.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "sseq1d.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wrex.mm"
include "simpr.mm"
include "adantlr.mm"
include "simplr.mm"
include "absled.mm"
include "ancom.mm"
include "lenegcon1.mm"
include "syl2anc.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "biimpd.mm"
include "breq2.mm"
include "anbi1d.mm"
include "rexralbidv.mm"
include "rspc2ev.mm"
include "3anidm12.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "cif.mm"
include "simplrr.mm"
include "wn.mm"
include "simplrl.mm"
include "ifclda.mm"
include "max2.mm"
include "ad2antlr.mm"
include "renegcld.mm"
include "ifcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylibd.mm"
include "max1.mm"
include "anim12d.mm"
include "ancomsd.mm"
include "sylibrd.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "rspcev.mm"
include "rexlimdvva.mm"
include "impbid.mm"
include "rexanre.mm"
include "adantl.mm"
include "2rexbidv.mm"
include "reeanv.mm"
include "syl6bb.mm"
include "rexcom.mm"
include "anbi12i.mm"
include "3bitr4g.mm"
include "recnd.mm"
include "elo1mpt.mm"
include "ello1mpt.mm"
include "anbi12d.mm"
include "3bitr4d.mm"
include "ex.mm"
include "sylbid.mm"
include "pm5.21ndd.mm"

theorem o1lo1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let cM: class M
  assume o1lo1.1: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint M x
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> ( ( x e. A |-> B ) e. O(1) <-> ( ( x e. A |-> B ) e. <_O(1) /\ ( x e. A |-> -u B ) e. <_O(1) ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    cr
    wss
    #
    @0
    co1
    wcel
    #
    @0
    clo1
    wcel
    #
    vx
    cA
    cB
    cneg
    #
    cmpt
    clo1
    wcel
    #
    wa
    #
    @3
    @2
    wi
    wph
    @0
    o1dm
    a1i
    @7
    @2
    wi
    wph
    @4
    @2
    @6
    @0
    lo1dm
    adantr
    a1i
    wph
    @2
    cA
    cr
    wss
    #
    @3
    @7
    wb
    #
    wph
    @1
    cA
    cr
    wph
    cB
    cr
    wcel
    #
    vx
    cA
    wral
    @1
    cA
    wceq
    wph
    @10
    vx
    cA
    o1lo1.1
    ralrimiva
    vx
    cA
    cB
    cr
    dmmptg
    syl
    sseq1d
    wph
    @8
    @9
    wph
    @8
    wa
    #
    vc
    cv
    vx
    cv
    #
    cle
    wbr
    #
    cB
    cabs
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    vc
    cr
    wrex
    #
    @13
    cB
    vn
    cv
    #
    cle
    wbr
    #
    wi
    vx
    cA
    wral
    #
    vn
    cr
    wrex
    vc
    cr
    wrex
    #
    @13
    @5
    vp
    cv
    #
    cle
    wbr
    #
    wi
    vx
    cA
    wral
    #
    vp
    cr
    wrex
    vc
    cr
    wrex
    #
    wa
    #
    @3
    @7
    @11
    @18
    vc
    cr
    wrex
    #
    vm
    cr
    wrex
    #
    @22
    vc
    cr
    wrex
    #
    vn
    cr
    wrex
    #
    @26
    vc
    cr
    wrex
    #
    vp
    cr
    wrex
    #
    wa
    #
    @19
    @28
    @11
    @30
    @31
    @33
    wa
    #
    vp
    cr
    wrex
    vn
    cr
    wrex
    #
    @35
    @11
    @30
    @13
    @21
    @25
    wa
    #
    wi
    #
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    vp
    cr
    wrex
    vn
    cr
    wrex
    #
    @37
    @11
    @30
    @42
    @11
    @29
    @42
    vm
    cr
    @11
    @15
    cr
    wcel
    #
    wa
    #
    @43
    @29
    @13
    cB
    @15
    cle
    wbr
    #
    @5
    @15
    cle
    wbr
    #
    wa
    #
    wi
    #
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    @42
    @11
    @43
    simpr
    @44
    @29
    @50
    @44
    @18
    @49
    vc
    cr
    @44
    @17
    @48
    vx
    cA
    @44
    @12
    cA
    wcel
    #
    wa
    #
    @16
    @47
    @13
    @52
    @16
    @15
    cneg
    cB
    cle
    wbr
    #
    @45
    wa
    #
    @47
    @52
    cB
    @15
    @11
    @51
    @10
    @43
    wph
    @51
    @10
    @8
    o1lo1.1
    adantlr
    #
    adantlr
    #
    @11
    @43
    @51
    simplr
    #
    absled
    @54
    @45
    @53
    wa
    @52
    @47
    @53
    @45
    ancom
    @52
    @53
    @46
    @45
    @52
    @43
    @10
    @53
    @46
    wb
    @57
    @56
    @15
    cB
    lenegcon1
    syl2anc
    anbi2d
    syl5bb
    bitrd
    imbi2d
    ralbidva
    rexbidv
    biimpd
    @43
    @50
    @42
    @41
    @50
    @13
    @45
    @25
    wa
    #
    wi
    #
    vx
    cA
    wral
    vc
    cr
    wrex
    vn
    vp
    @15
    @15
    cr
    cr
    @20
    @15
    wceq
    #
    @39
    @59
    vc
    vx
    cr
    cA
    @60
    @38
    @58
    @13
    @60
    @21
    @45
    @25
    @20
    @15
    cB
    cle
    breq2
    anbi1d
    imbi2d
    rexralbidv
    @24
    @15
    wceq
    #
    @59
    @48
    vc
    vx
    cr
    cA
    @61
    @58
    @47
    @13
    @61
    @25
    @46
    @45
    @24
    @15
    @5
    cle
    breq2
    anbi2d
    imbi2d
    rexralbidv
    rspc2ev
    3anidm12
    syl6an
    rexlimdva
    @11
    @41
    @30
    vn
    vp
    cr
    cr
    @11
    @20
    cr
    wcel
    #
    @24
    cr
    wcel
    #
    wa
    #
    wa
    #
    @20
    @24
    cle
    wbr
    #
    @24
    @20
    cif
    #
    cr
    wcel
    #
    @41
    @13
    @14
    @67
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    @30
    @65
    @66
    @24
    @20
    cr
    @11
    @62
    @63
    @66
    simplrr
    @11
    @62
    @63
    @66
    wn
    simplrl
    ifclda
    @65
    @40
    @71
    vc
    cr
    @65
    @39
    @70
    vx
    cA
    @65
    @51
    wa
    #
    @38
    @69
    @13
    @73
    @38
    @67
    cneg
    cB
    cle
    wbr
    #
    cB
    @67
    cle
    wbr
    #
    wa
    #
    @69
    @73
    @25
    @21
    @76
    @73
    @25
    @74
    @21
    @75
    @73
    @25
    @5
    @67
    cle
    wbr
    #
    @74
    @73
    @25
    @24
    @67
    cle
    wbr
    #
    @77
    @64
    @78
    @11
    @51
    @20
    @24
    max2
    ad2antlr
    @73
    @5
    cr
    wcel
    @63
    @68
    @25
    @78
    wa
    @77
    wi
    @73
    cB
    @11
    @51
    @10
    @64
    @55
    adantlr
    #
    renegcld
    @11
    @62
    @63
    @51
    simplrr
    #
    @73
    @66
    @24
    @20
    cr
    @80
    @11
    @62
    @63
    @51
    simplrl
    #
    ifcld
    #
    @5
    @24
    @67
    letr
    syl3anc
    mpan2d
    @73
    @10
    @68
    @77
    @74
    wb
    @79
    @82
    cB
    @67
    lenegcon1
    syl2anc
    sylibd
    @73
    @21
    @20
    @67
    cle
    wbr
    #
    @75
    @64
    @83
    @11
    @51
    @20
    @24
    max1
    ad2antlr
    @73
    @10
    @62
    @68
    @21
    @83
    wa
    @75
    wi
    @79
    @81
    @82
    cB
    @20
    @67
    letr
    syl3anc
    mpan2d
    anim12d
    ancomsd
    @73
    cB
    @67
    @79
    @82
    absled
    sylibrd
    imim2d
    ralimdva
    reximdv
    @29
    @72
    vm
    @67
    cr
    @15
    @67
    wceq
    #
    @17
    @70
    vc
    vx
    cr
    cA
    @84
    @16
    @69
    @13
    @15
    @67
    @14
    cle
    breq2
    imbi2d
    rexralbidv
    rspcev
    syl6an
    rexlimdvva
    impbid
    @11
    @41
    @36
    vn
    vp
    cr
    cr
    @8
    @41
    @36
    wb
    wph
    @21
    @25
    cA
    vc
    vx
    rexanre
    adantl
    2rexbidv
    bitrd
    @31
    @33
    vn
    vp
    cr
    cr
    reeanv
    syl6bb
    @18
    vc
    vm
    cr
    cr
    rexcom
    @23
    @32
    @27
    @34
    @22
    vc
    vn
    cr
    cr
    rexcom
    @26
    vc
    vp
    cr
    cr
    rexcom
    anbi12i
    3bitr4g
    @11
    vx
    vc
    cA
    cB
    vm
    wph
    @8
    simpr
    #
    @11
    @51
    wa
    #
    cB
    @55
    recnd
    elo1mpt
    @11
    @4
    @23
    @6
    @27
    @11
    vx
    vc
    cA
    cB
    vn
    @85
    @55
    ello1mpt
    @11
    vx
    vc
    cA
    @5
    vp
    @85
    @86
    cB
    @55
    renegcld
    ello1mpt
    anbi12d
    3bitr4d
    ex
    sylbid
    pm5.21ndd
end
