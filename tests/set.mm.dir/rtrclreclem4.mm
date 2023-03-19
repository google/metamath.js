include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "w3a.mm"
include "crtrcl.mm"
include "cfv.mm"
include "wi.mm"
include "cvv.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqidd.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "adantl.mm"
include "wcel.mm"
include "nn0ex.mm"
include "ovex.mm"
include "iunex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "wa.mm"
include "wral.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "cuni.mm"
include "simprl.mm"
include "relexp0d.mm"
include "syl.mm"
include "wrel.mm"
include "relfld.mm"
include "simprrr.mm"
include "reseq2.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "eqsstrd.mm"
include "simprrl.mm"
include "jca32.mm"
include "mpd.mm"
include "relexpsucrd.mm"
include "coss2.mm"
include "coss1.mm"
include "sylan9ss.mm"
include "sstrd.mm"
include "mpancom.mm"
include "expcom.mm"
include "anassrs.mm"
include "impcom.mm"
include "nn0ind.mm"
include "anabsi5.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "3imp1.mm"
include "sseq1.mm"
include "imbi2d.mm"
include "wb.mm"
include "df-rtrclrec.mm"
include "fveq1.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "alrimiv.mm"

theorem rtrclreclem4
  let wph: wff ph
  let cR: class R
  let vs: setvar s
  let vn: setvar n
  let vi: setvar i
  let vm: setvar m
  let vr: setvar r
  assume rtrclreclem.rel: |- ( ph -> Rel R )
  assume rtrclreclem.rex: |- ( ph -> R e. _V )

  disjoint ph s
  disjoint n ph
  disjoint i ph
  disjoint n s
  disjoint i s
  disjoint i n
  disjoint m ph
  disjoint m s
  disjoint i m
  disjoint ph r
  disjoint n r
  disjoint R r
  disjoint R n
  disjoint R i
  disjoint R m
  assert |- ( ph -> A. s ( ( ( _I |` ( dom R u. ran R ) ) C_ s /\ R C_ s /\ ( s o. s ) C_ s ) -> ( t*rec ` R ) C_ s ) )

  proof
    wph
    cid
    cR
    cdm
    cR
    crn
    cun
    #
    cres
    #
    vs
    cv
    #
    wss
    #
    cR
    @2
    wss
    #
    @2
    @2
    ccom
    #
    @2
    wss
    #
    w3a
    #
    cR
    crtrcl
    cfv
    #
    @2
    wss
    #
    wi
    #
    vs
    wph
    @10
    wi
    #
    wph
    @7
    cR
    vr
    cvv
    vn
    cn0
    vr
    cv
    #
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cmpt
    #
    cfv
    #
    @2
    wss
    #
    wi
    #
    wi
    #
    @17
    vn
    cn0
    cR
    @13
    crelexp
    co
    #
    ciun
    #
    wceq
    #
    wph
    @19
    wph
    vr
    cR
    @15
    @22
    cvv
    @16
    cvv
    wph
    @16
    eqidd
    @12
    cR
    wceq
    #
    @15
    @22
    wceq
    wph
    @24
    vn
    cn0
    @14
    @21
    @12
    cR
    @13
    crelexp
    oveq1
    iuneq2d
    adantl
    rtrclreclem.rex
    @22
    cvv
    wcel
    wph
    vn
    cn0
    @21
    nn0ex
    cR
    @13
    crelexp
    ovex
    iunex
    a1i
    fvmptd
    wph
    @19
    @23
    @7
    @22
    @2
    wss
    #
    wi
    @7
    wph
    @25
    @3
    @4
    @6
    wph
    @25
    @4
    @3
    @6
    wph
    @25
    wi
    #
    wi
    @6
    @4
    @3
    wa
    #
    @26
    wph
    @6
    @27
    wa
    #
    @25
    wph
    @28
    wa
    #
    @21
    @2
    wss
    #
    vn
    cn0
    wral
    @25
    @29
    @30
    vn
    cn0
    @13
    cn0
    wcel
    #
    @29
    @30
    @31
    @29
    @30
    vi
    cv
    #
    cn0
    wcel
    #
    @29
    wa
    #
    cR
    @32
    crelexp
    co
    #
    @2
    wss
    #
    wi
    cc0
    cn0
    wcel
    #
    @29
    wa
    #
    cR
    cc0
    crelexp
    co
    #
    @2
    wss
    #
    wi
    vm
    cv
    #
    cn0
    wcel
    #
    @29
    wa
    #
    cR
    @41
    crelexp
    co
    #
    @2
    wss
    #
    wi
    #
    @41
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    @29
    wa
    #
    cR
    @47
    crelexp
    co
    #
    @2
    wss
    #
    wi
    #
    @31
    @29
    wa
    #
    @30
    wi
    vi
    vm
    @13
    @32
    cc0
    wceq
    #
    @34
    @38
    @36
    @40
    @54
    @33
    @37
    @29
    @32
    cc0
    cn0
    eleq1
    anbi1d
    @54
    @35
    @39
    @2
    @32
    cc0
    cR
    crelexp
    oveq2
    sseq1d
    imbi12d
    @32
    @41
    wceq
    #
    @34
    @43
    @36
    @45
    @55
    @33
    @42
    @29
    @32
    @41
    cn0
    eleq1
    anbi1d
    @55
    @35
    @44
    @2
    @32
    @41
    cR
    crelexp
    oveq2
    sseq1d
    imbi12d
    @32
    @47
    wceq
    #
    @34
    @49
    @36
    @51
    @56
    @33
    @48
    @29
    @32
    @47
    cn0
    eleq1
    anbi1d
    @56
    @35
    @50
    @2
    @32
    @47
    cR
    crelexp
    oveq2
    sseq1d
    imbi12d
    @32
    @13
    wceq
    #
    @34
    @53
    @36
    @30
    @57
    @33
    @31
    @29
    @32
    @13
    cn0
    eleq1
    anbi1d
    @57
    @35
    @21
    @2
    @32
    @13
    cR
    crelexp
    oveq2
    sseq1d
    imbi12d
    @38
    @39
    cid
    cR
    cuni
    cuni
    #
    cres
    #
    @2
    @38
    wph
    @39
    @59
    wceq
    @37
    wph
    @28
    simprl
    #
    wph
    cR
    rtrclreclem.rel
    rtrclreclem.rex
    relexp0d
    syl
    @58
    @0
    wceq
    #
    @38
    @59
    @2
    wss
    #
    @38
    cR
    wrel
    #
    @61
    @38
    wph
    @63
    @60
    rtrclreclem.rel
    syl
    cR
    relfld
    syl
    @38
    @62
    @61
    @3
    @29
    @3
    @37
    wph
    @6
    @4
    @3
    simprrr
    adantl
    @61
    @59
    @1
    @2
    @58
    @0
    cid
    reseq2
    sseq1d
    syl5ibr
    mpcom
    eqsstrd
    @46
    @42
    @52
    @49
    @46
    @42
    wa
    #
    @51
    @48
    @29
    @64
    @51
    @29
    @64
    wa
    @48
    @51
    wph
    @28
    @64
    @48
    @51
    wi
    #
    @28
    @64
    wa
    wph
    @65
    @6
    @27
    @64
    wph
    @65
    wi
    #
    @27
    @64
    wa
    @6
    @66
    @4
    @3
    @64
    @6
    @66
    wi
    @6
    @4
    @3
    @64
    wa
    #
    wa
    #
    @66
    wph
    @6
    @68
    wa
    #
    @65
    @48
    wph
    @69
    wa
    #
    @51
    @45
    @48
    @70
    wa
    #
    @51
    @71
    @43
    @45
    @71
    @42
    wph
    @28
    @70
    @42
    @48
    @69
    @42
    wph
    @68
    @42
    @6
    @4
    @3
    @46
    @42
    simprrr
    adantl
    adantl
    adantl
    #
    @48
    wph
    @69
    simprl
    @71
    @6
    @4
    @3
    @48
    wph
    @6
    @68
    simprrl
    #
    @70
    @4
    @48
    wph
    @6
    @4
    @67
    simprrl
    adantl
    #
    @70
    @3
    @48
    @69
    @3
    wph
    @6
    @4
    @3
    @64
    simprrl
    adantl
    adantl
    jca32
    jca32
    @70
    @46
    @48
    @69
    @46
    wph
    @68
    @46
    @6
    @4
    @3
    @46
    @42
    simprrl
    adantl
    adantl
    adantl
    mpd
    @45
    @71
    wa
    #
    @50
    @44
    cR
    ccom
    #
    @2
    @75
    @42
    @50
    @76
    wceq
    @71
    @42
    @45
    @72
    adantl
    @75
    cR
    @41
    @75
    wph
    @63
    @45
    @48
    wph
    @69
    simprrl
    #
    rtrclreclem.rel
    syl
    @75
    wph
    cR
    cvv
    wcel
    @77
    rtrclreclem.rex
    syl
    relexpsucrd
    mpd
    @75
    @76
    @44
    @2
    ccom
    #
    @2
    @75
    @4
    @76
    @78
    wss
    @71
    @4
    @45
    @74
    adantl
    cR
    @2
    @44
    coss2
    syl
    @45
    @71
    @78
    @5
    @2
    @44
    @2
    @2
    coss1
    @73
    sylan9ss
    sstrd
    eqsstrd
    mpancom
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
    nn0ind
    anabsi5
    expcom
    ralrimiv
    vn
    cn0
    @21
    @2
    iunss
    sylibr
    expcom
    expcom
    expcom
    3imp1
    expcom
    @23
    @18
    @25
    @7
    @17
    @22
    @2
    sseq1
    imbi2d
    syl5ibr
    mpcom
    crtrcl
    @16
    wceq
    #
    @11
    @20
    wb
    vn
    vr
    df-rtrclrec
    @79
    @10
    @19
    wph
    @79
    @9
    @18
    @7
    @79
    @8
    @17
    @2
    cR
    crtrcl
    @16
    fveq1
    sseq1d
    imbi2d
    imbi2d
    ax-mp
    mpbir
    alrimiv
end
