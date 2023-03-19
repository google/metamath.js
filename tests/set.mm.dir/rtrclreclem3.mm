include "crtrcl.mm"
include "cfv.mm"
include "ccom.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wceq.mm"
include "wcel.mm"
include "wi.mm"
include "df-co.mm"
include "cop.mm"
include "elopab.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "simprr.mm"
include "simprl.mm"
include "crelexp.mm"
include "co.mm"
include "cn0.mm"
include "wrex.mm"
include "simpl.mm"
include "wb.mm"
include "dfrtrclrec2.mm"
include "syl.mm"
include "mpbid.mm"
include "simprrl.mm"
include "caddc.mm"
include "adantl.mm"
include "nn0addcld.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "eleq1.mm"
include "wrel.mm"
include "cvv.mm"
include "relexpaddd.mm"
include "mp2and.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "syl5ibr.mm"
include "sylbid.mm"
include "mpcom.mm"
include "eqcomd.mm"
include "vex.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "brco.mm"
include "sylibr.mm"
include "breq.mm"
include "breqd.mm"
include "rspcev.mm"
include "syldan.mm"
include "mpancom.mm"
include "df-br.mm"
include "syl5bbr.mm"
include "mpbird.mm"
include "expcom.mm"
include "anassrs.mm"
include "impcom.mm"
include "rexlimiv.mm"
include "exlimdv.mm"
include "sylc.mm"
include "anabsi5.mm"
include "exlimdvv.mm"
include "syl5bi.mm"
include "eleq2.mm"
include "imbi1d.mm"
include "ax-mp.mm"
include "ssrdv.mm"

theorem rtrclreclem3
  let wph: wff ph
  let cR: class R
  let vd: setvar d
  let ve: setvar e
  let vg: setvar g
  let vf: setvar f
  let vn: setvar n
  let vm: setvar m
  let vh: setvar h
  let vi: setvar i
  assume rtrclreclem.rel: |- ( ph -> Rel R )
  assume rtrclreclem.rex: |- ( ph -> R e. _V )


  assert |- ( ph -> ( ( t*rec ` R ) o. ( t*rec ` R ) ) C_ ( t*rec ` R ) )

  proof
    wph
    vd
    cR
    crtrcl
    cfv
    #
    @0
    ccom
    #
    @0
    @1
    ve
    cv
    #
    vf
    cv
    #
    @0
    wbr
    #
    @3
    vg
    cv
    #
    @0
    wbr
    #
    wa
    #
    vf
    wex
    #
    ve
    vg
    copab
    #
    wceq
    #
    wph
    vd
    cv
    #
    @1
    wcel
    #
    @11
    @0
    wcel
    #
    wi
    #
    wi
    ve
    vg
    vf
    @0
    @0
    df-co
    wph
    @14
    @10
    @11
    @9
    wcel
    #
    @13
    wi
    @15
    @11
    @2
    @5
    cop
    #
    wceq
    #
    @8
    wa
    #
    vg
    wex
    ve
    wex
    wph
    @13
    @8
    ve
    vg
    @11
    elopab
    wph
    @18
    @13
    ve
    vg
    @18
    wph
    @13
    @17
    @8
    wph
    @13
    @17
    @8
    wph
    wa
    #
    @13
    @17
    @17
    @19
    wa
    @16
    @16
    wceq
    #
    @19
    wa
    #
    @13
    @17
    @17
    @20
    @19
    @11
    @16
    @16
    eqeq1
    anbi1d
    @21
    @13
    @17
    @16
    @0
    wcel
    #
    @21
    wph
    @8
    @22
    @20
    @8
    wph
    simprr
    @20
    @8
    wph
    simprl
    wph
    @7
    @22
    vf
    @7
    wph
    @22
    @4
    @6
    wph
    @22
    @2
    @3
    cR
    vn
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vn
    cn0
    wrex
    #
    @4
    @6
    wph
    wa
    #
    wa
    #
    @22
    @28
    @4
    @26
    @4
    @27
    simpl
    @28
    wph
    @4
    @26
    wb
    @4
    @6
    wph
    simprr
    wph
    @2
    @3
    cR
    vn
    rtrclreclem.rel
    rtrclreclem.rex
    dfrtrclrec2
    syl
    mpbid
    @25
    @28
    @22
    wi
    #
    vn
    cn0
    @25
    @23
    cn0
    wcel
    #
    @29
    @28
    @25
    @30
    wa
    #
    @22
    @4
    @27
    @31
    @22
    @27
    @31
    wa
    @4
    @22
    @6
    wph
    @31
    @4
    @22
    wi
    #
    @4
    @6
    wph
    @31
    wa
    #
    wa
    #
    @22
    @3
    @5
    cR
    vm
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vm
    cn0
    wrex
    #
    @4
    @34
    wa
    #
    @22
    @39
    @6
    @38
    @4
    @6
    @33
    simprl
    @39
    wph
    @6
    @38
    wb
    @4
    @6
    wph
    @31
    simprrl
    wph
    @3
    @5
    cR
    vm
    rtrclreclem.rel
    rtrclreclem.rex
    dfrtrclrec2
    syl
    mpbid
    @37
    @39
    @22
    wi
    #
    vm
    cn0
    @37
    @35
    cn0
    wcel
    #
    @40
    @39
    @37
    @41
    wa
    #
    @22
    @4
    @34
    @42
    @22
    @34
    @42
    wa
    @4
    @22
    @6
    @33
    @42
    @32
    @33
    @42
    wa
    @6
    @32
    wph
    @31
    @42
    @6
    @32
    wi
    #
    @31
    @42
    wa
    wph
    @43
    @25
    @30
    @42
    wph
    @43
    wi
    wph
    @25
    @30
    @42
    wa
    #
    wa
    #
    @43
    @6
    wph
    @45
    wa
    #
    @32
    @4
    @6
    @46
    wa
    #
    @22
    @4
    @47
    wa
    #
    @22
    @2
    @5
    cR
    vi
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vi
    cn0
    wrex
    #
    @23
    @35
    caddc
    co
    #
    cn0
    wcel
    #
    @48
    @52
    @48
    @23
    @35
    @47
    @30
    @4
    @46
    @30
    @6
    wph
    @25
    @30
    @42
    simprrl
    adantl
    adantl
    #
    @47
    @41
    @4
    @46
    @41
    @6
    @45
    @41
    wph
    @44
    @41
    @25
    @30
    @37
    @41
    simprr
    adantl
    adantl
    adantl
    adantl
    #
    nn0addcld
    @54
    @48
    @2
    @5
    cR
    @53
    crelexp
    co
    #
    wbr
    #
    @52
    @57
    @36
    @24
    ccom
    #
    wceq
    #
    @54
    @48
    wa
    #
    @58
    @61
    @59
    @57
    @53
    @35
    @23
    caddc
    co
    #
    wceq
    #
    @61
    @59
    @57
    wceq
    #
    @61
    @23
    @35
    @61
    @23
    @48
    @30
    @54
    @55
    adantl
    nn0cnd
    @61
    @35
    @48
    @41
    @54
    @56
    adantl
    nn0cnd
    addcomd
    @63
    @61
    @62
    cn0
    wcel
    #
    @48
    wa
    #
    @64
    @63
    @54
    @65
    @48
    @53
    @62
    cn0
    eleq1
    anbi1d
    @66
    @64
    @63
    @59
    cR
    @62
    crelexp
    co
    #
    wceq
    #
    @66
    @41
    @30
    @68
    @48
    @41
    @65
    @56
    adantl
    @48
    @30
    @65
    @55
    adantl
    @66
    cR
    @23
    @35
    @66
    wph
    cR
    wrel
    #
    @48
    wph
    @65
    @4
    @6
    wph
    @45
    simprrl
    #
    adantl
    #
    rtrclreclem.rel
    syl
    @66
    wph
    cR
    cvv
    wcel
    #
    @71
    rtrclreclem.rex
    syl
    relexpaddd
    mp2and
    @63
    @57
    @67
    @59
    @53
    @62
    cR
    crelexp
    oveq2
    eqeq2d
    syl5ibr
    sylbid
    mpcom
    eqcomd
    @61
    @58
    @60
    @2
    @5
    @59
    wbr
    #
    @61
    @2
    vh
    cv
    #
    @24
    wbr
    #
    @74
    @5
    @36
    wbr
    #
    wa
    #
    vh
    wex
    #
    @73
    @61
    @25
    @37
    @78
    @48
    @25
    @54
    @47
    @25
    @4
    @6
    wph
    @25
    @44
    simprrl
    adantl
    adantl
    @48
    @37
    @54
    @47
    @37
    @4
    @46
    @37
    @6
    @45
    @37
    wph
    @25
    @30
    @37
    @41
    simprrl
    adantl
    adantl
    adantl
    adantl
    @77
    @25
    @37
    wa
    vh
    @3
    vf
    vex
    @74
    @3
    wceq
    @75
    @25
    @76
    @37
    @74
    @3
    @2
    @24
    breq2
    @74
    @3
    @5
    @36
    breq1
    anbi12d
    spcev
    syl2anc
    vh
    @2
    @5
    @36
    @24
    ve
    vex
    vg
    vex
    brco
    sylibr
    @2
    @5
    @57
    @59
    breq
    syl5ibr
    mpcom
    @51
    @58
    vi
    @53
    cn0
    @49
    @53
    wceq
    @50
    @57
    @2
    @5
    @49
    @53
    cR
    crelexp
    oveq2
    breqd
    rspcev
    syldan
    mpancom
    @22
    @2
    @5
    @0
    wbr
    @48
    @52
    @2
    @5
    @0
    df-br
    @48
    @2
    @5
    cR
    vi
    @48
    wph
    @69
    @70
    rtrclreclem.rel
    syl
    @48
    wph
    @72
    @70
    rtrclreclem.rex
    syl
    dfrtrclrec2
    syl5bbr
    mpbird
    expcom
    expcom
    expcom
    anassrs
    impcom
    anassrs
    impcom
    anassrs
    impcom
    anassrs
    expcom
    expcom
    rexlimiv
    mpcom
    expcom
    anassrs
    impcom
    anassrs
    expcom
    expcom
    rexlimiv
    mpcom
    anassrs
    expcom
    exlimdv
    sylc
    @11
    @16
    @0
    eleq1
    syl5ibr
    sylbid
    anabsi5
    anassrs
    expcom
    exlimdvv
    syl5bi
    @10
    @12
    @15
    @13
    @1
    @9
    @11
    eleq2
    imbi1d
    syl5ibr
    ax-mp
    ssrdv
end
