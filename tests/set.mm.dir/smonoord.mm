include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "cmin.mm"
include "wral.mm"
include "eluzp1m1.mm"
include "syl2anc.mm"
include "eluzfz1.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "a1d.mm"
include "a1i.mm"
include "wa.mm"
include "peano2fzr.mm"
include "adantll.mm"
include "ex.mm"
include "imim1d.mm"
include "peano2uzr.mm"
include "syl11.mm"
include "adantr.mm"
include "impcom.mm"
include "eluzelz.mm"
include "adantl.mm"
include "elfzuz3.mm"
include "ad2antll.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "cr.mm"
include "cle.mm"
include "zre.mm"
include "lep1d.mm"
include "jccir.mm"
include "eluzuzle.mm"
include "eleq1d.mm"
include "wss.mm"
include "fzp1ss.mm"
include "sseld.mm"
include "com12.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "expr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem smonoord
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  assume smonoord.0: |- ( ph -> M e. ZZ )
  assume smonoord.1: |- ( ph -> N e. ( ZZ>= ` ( M + 1 ) ) )
  assume smonoord.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR )
  assume smonoord.3: |- ( ( ph /\ k e. ( M ... ( N - 1 ) ) ) -> ( F ` k ) < ( F ` ( k + 1 ) ) )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( F ` M ) < ( F ` N ) )

  proof
    wph
    cN
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    cM
    cF
    cfv
    #
    cN
    cF
    cfv
    #
    clt
    wbr
    #
    wph
    cN
    @0
    cuz
    cfv
    #
    wcel
    #
    @2
    smonoord.1
    @0
    cN
    eluzfz2
    syl
    @7
    wph
    @2
    @5
    wi
    #
    smonoord.1
    wph
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @9
    cF
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    wph
    @0
    @1
    wcel
    #
    @3
    @0
    cF
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    #
    wph
    vn
    cv
    #
    @1
    wcel
    #
    @3
    @19
    cF
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    wph
    @19
    c1
    caddc
    co
    #
    @1
    wcel
    #
    @3
    @24
    cF
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    wph
    @8
    wi
    vx
    vn
    @0
    cN
    @9
    @0
    wceq
    #
    @13
    @17
    wph
    @29
    @10
    @14
    @12
    @16
    @9
    @0
    @1
    eleq1
    @29
    @11
    @15
    @3
    clt
    @9
    @0
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    vx
    vn
    weq
    #
    @13
    @23
    wph
    @30
    @10
    @20
    @12
    @22
    @9
    @19
    @1
    eleq1
    @30
    @11
    @21
    @3
    clt
    @9
    @19
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @9
    @24
    wceq
    #
    @13
    @28
    wph
    @31
    @10
    @25
    @12
    @27
    @9
    @24
    @1
    eleq1
    @31
    @11
    @26
    @3
    clt
    @9
    @24
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @9
    cN
    wceq
    #
    @13
    @8
    wph
    @32
    @10
    @2
    @12
    @5
    @9
    cN
    @1
    eleq1
    @32
    @11
    @4
    @3
    clt
    @9
    cN
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @18
    @0
    cz
    wcel
    wph
    @16
    @14
    wph
    cM
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @36
    c1
    caddc
    co
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vk
    @34
    wral
    #
    @16
    wph
    @33
    cM
    cuz
    cfv
    #
    wcel
    #
    @35
    wph
    cM
    cz
    wcel
    #
    @7
    @43
    smonoord.0
    smonoord.1
    cM
    cN
    eluzp1m1
    syl2anc
    cM
    @33
    eluzfz1
    syl
    wph
    @40
    vk
    @34
    smonoord.3
    ralrimiva
    #
    @40
    @16
    vk
    cM
    @34
    @36
    cM
    wceq
    #
    @37
    @3
    @39
    @15
    clt
    @36
    cM
    cF
    fveq2
    #
    @46
    @38
    @0
    cF
    @36
    cM
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspcv
    sylc
    a1d
    a1i
    @19
    @6
    wcel
    #
    wph
    @23
    @28
    wph
    @48
    @23
    @28
    wi
    wph
    @48
    wa
    #
    @23
    @25
    @22
    wi
    @28
    @49
    @25
    @20
    @22
    @49
    @25
    @20
    @48
    @25
    @20
    wph
    @19
    @0
    cN
    peano2fzr
    adantll
    ex
    imim1d
    @49
    @25
    @22
    @27
    wph
    @48
    @25
    @22
    @27
    wi
    wph
    @48
    @25
    wa
    #
    wa
    #
    @22
    @21
    @26
    clt
    wbr
    #
    @27
    @51
    @19
    @34
    wcel
    #
    @41
    @52
    @51
    @19
    @42
    wcel
    #
    @33
    @19
    cuz
    cfv
    wcel
    #
    @53
    @50
    wph
    @54
    @48
    wph
    @54
    wi
    @25
    @44
    @48
    @54
    wph
    @44
    @48
    @54
    cM
    @19
    peano2uzr
    ex
    smonoord.0
    syl11
    adantr
    impcom
    #
    @51
    @19
    cz
    wcel
    #
    cN
    @24
    cuz
    cfv
    wcel
    #
    @55
    @50
    @57
    wph
    @48
    @57
    @25
    @0
    @19
    eluzelz
    adantr
    adantl
    @25
    @58
    wph
    @48
    @24
    @0
    cN
    elfzuz3
    ad2antll
    @19
    cN
    eluzp1m1
    syl2anc
    @19
    cM
    @33
    elfzuzb
    sylanbrc
    wph
    @41
    @50
    @45
    adantr
    @40
    @52
    vk
    @19
    @34
    vk
    vn
    weq
    #
    @37
    @21
    @39
    @26
    clt
    @36
    @19
    cF
    fveq2
    #
    @59
    @38
    @24
    cF
    @36
    @19
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspcv
    sylc
    @51
    @3
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @26
    cr
    wcel
    #
    @22
    @52
    wa
    @27
    wi
    wph
    @61
    @50
    wph
    cM
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @37
    cr
    wcel
    #
    vk
    @64
    wral
    #
    @61
    wph
    cN
    @42
    wcel
    #
    @65
    wph
    @44
    cM
    @0
    cle
    wbr
    #
    wa
    @7
    @68
    wph
    @44
    @69
    smonoord.0
    @44
    cM
    cM
    zre
    lep1d
    jccir
    smonoord.1
    @0
    cM
    cN
    eluzuzle
    sylc
    cM
    cN
    eluzfz1
    syl
    wph
    @66
    vk
    @64
    smonoord.2
    ralrimiva
    #
    @66
    @61
    vk
    cM
    @64
    @46
    @37
    @3
    cr
    @47
    eleq1d
    rspcv
    sylc
    adantr
    @51
    @19
    @64
    wcel
    #
    @67
    @62
    @51
    @54
    @24
    @64
    wcel
    #
    @71
    @56
    @50
    wph
    @72
    @25
    wph
    @72
    wi
    @48
    wph
    @25
    @72
    wph
    @1
    @64
    @24
    wph
    @44
    @1
    @64
    wss
    smonoord.0
    cM
    cN
    fzp1ss
    syl
    sseld
    com12
    adantl
    impcom
    #
    @19
    cM
    cN
    peano2fzr
    syl2anc
    wph
    @67
    @50
    @70
    adantr
    #
    @66
    @62
    vk
    @19
    @64
    @59
    @37
    @21
    cr
    @60
    eleq1d
    rspcv
    sylc
    @51
    @72
    @67
    @63
    @73
    @74
    @66
    @63
    vk
    @24
    @64
    @36
    @24
    wceq
    @37
    @26
    cr
    @36
    @24
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    @3
    @21
    @26
    lttr
    syl3anc
    mpan2d
    expr
    a2d
    syld
    expcom
    a2d
    uzind4
    mpcom
    mpd
end
