include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "renegcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "fzp1elp1.mm"
include "adantl.mm"
include "cc.mm"
include "cuz.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fzssp1.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "lenegd.mm"
include "mpbid.mm"
include "negeqd.mm"
include "negex.mm"
include "fvmpt.mm"
include "3brtr4d.mm"
include "monoord.mm"
include "eluzfz1.mm"
include "eluzfz2.mm"
include "3brtr3d.mm"
include "mpbird.mm"

theorem monoord2
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume monoord2.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume monoord2.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR )
  assume monoord2.3: |- ( ( ph /\ k e. ( M ... ( N - 1 ) ) ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint k n
  disjoint F n
  disjoint M n
  disjoint N n
  disjoint n ph
  assert |- ( ph -> ( F ` N ) <_ ( F ` M ) )

  proof
    wph
    cN
    cF
    cfv
    #
    cM
    cF
    cfv
    #
    cle
    wbr
    @1
    cneg
    #
    @0
    cneg
    #
    cle
    wbr
    wph
    cM
    vk
    cM
    cN
    cfz
    co
    #
    vk
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    cN
    @8
    cfv
    #
    @2
    @3
    cle
    wph
    vn
    @8
    cM
    cN
    monoord2.1
    wph
    @4
    cr
    vn
    cv
    #
    @8
    wph
    vk
    @4
    @7
    cr
    @8
    wph
    @5
    @4
    wcel
    wa
    @6
    monoord2.2
    renegcld
    @8
    eqid
    #
    fmptd
    ffvelrnda
    wph
    @11
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
    wa
    #
    @11
    cF
    cfv
    #
    cneg
    #
    @11
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cneg
    #
    @11
    @8
    cfv
    #
    @19
    @8
    cfv
    #
    cle
    @16
    @20
    @17
    cle
    wbr
    #
    @18
    @21
    cle
    wbr
    wph
    @24
    vn
    @14
    wph
    @5
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @6
    cle
    wbr
    #
    vk
    @14
    wral
    @24
    vn
    @14
    wral
    wph
    @27
    vk
    @14
    monoord2.3
    ralrimiva
    @27
    @24
    vk
    vn
    @14
    @5
    @11
    wceq
    #
    @26
    @20
    @6
    @17
    cle
    @28
    @25
    @19
    cF
    @5
    @11
    c1
    caddc
    oveq1
    fveq2d
    @5
    @11
    cF
    fveq2
    #
    breq12d
    cbvralv
    sylib
    r19.21bi
    @16
    @20
    @17
    @16
    @19
    @4
    wcel
    #
    @6
    cr
    wcel
    #
    vk
    @4
    wral
    #
    @20
    cr
    wcel
    #
    @16
    @19
    cM
    @13
    c1
    caddc
    co
    #
    cfz
    co
    #
    @4
    @15
    @19
    @35
    wcel
    wph
    @11
    cM
    @13
    fzp1elp1
    adantl
    wph
    @35
    @4
    wceq
    @15
    wph
    @34
    cN
    cM
    cfz
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @34
    cN
    wceq
    wph
    cN
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    monoord2.1
    cM
    cN
    eluzelz
    syl
    zcnd
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq2d
    #
    adantr
    eleqtrd
    #
    wph
    @32
    @15
    wph
    @31
    vk
    @4
    monoord2.2
    ralrimiva
    #
    adantr
    #
    @31
    @33
    vk
    @19
    @4
    @5
    @19
    wceq
    #
    @6
    @20
    cr
    @5
    @19
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    @16
    @11
    @4
    wcel
    #
    @32
    @17
    cr
    wcel
    #
    wph
    @14
    @4
    @11
    wph
    @35
    @14
    @4
    cM
    @13
    fzssp1
    @37
    syl5sseq
    sselda
    #
    @40
    @31
    @44
    vk
    @11
    @4
    @28
    @6
    @17
    cr
    @29
    eleq1d
    rspcv
    sylc
    lenegd
    mpbid
    @16
    @43
    @22
    @18
    wceq
    @45
    vk
    @11
    @7
    @18
    @4
    @8
    @28
    @6
    @17
    @29
    negeqd
    @12
    @17
    negex
    fvmpt
    syl
    @16
    @30
    @23
    @21
    wceq
    @38
    vk
    @19
    @7
    @21
    @4
    @8
    @41
    @6
    @20
    @42
    negeqd
    @12
    @20
    negex
    fvmpt
    syl
    3brtr4d
    monoord
    wph
    cM
    @4
    wcel
    #
    @9
    @2
    wceq
    wph
    @36
    @46
    monoord2.1
    cM
    cN
    eluzfz1
    syl
    #
    vk
    cM
    @7
    @2
    @4
    @8
    @5
    cM
    wceq
    #
    @6
    @1
    @5
    cM
    cF
    fveq2
    #
    negeqd
    @12
    @1
    negex
    fvmpt
    syl
    wph
    cN
    @4
    wcel
    #
    @10
    @3
    wceq
    wph
    @36
    @50
    monoord2.1
    cM
    cN
    eluzfz2
    syl
    #
    vk
    cN
    @7
    @3
    @4
    @8
    @5
    cN
    wceq
    #
    @6
    @0
    @5
    cN
    cF
    fveq2
    #
    negeqd
    @12
    @0
    negex
    fvmpt
    syl
    3brtr3d
    wph
    @0
    @1
    wph
    @50
    @32
    @0
    cr
    wcel
    #
    @51
    @39
    @31
    @54
    vk
    cN
    @4
    @52
    @6
    @0
    cr
    @53
    eleq1d
    rspcv
    sylc
    wph
    @46
    @32
    @1
    cr
    wcel
    #
    @47
    @39
    @31
    @55
    vk
    cM
    @4
    @48
    @6
    @1
    cr
    @49
    eleq1d
    rspcv
    sylc
    lenegd
    mpbird
end
