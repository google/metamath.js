include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "cr.mm"
include "wral.mm"
include "eluzfz1.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "leidd.mm"
include "a1d.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "peano2fzr.mm"
include "syl2anc.mm"
include "expr.mm"
include "imim1d.mm"
include "cmin.mm"
include "eluzelz.mm"
include "elfzuz3.mm"
include "eluzp1m1.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "adantr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem monoord
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  assume monoord.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume monoord.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR )
  assume monoord.3: |- ( ( ph /\ k e. ( M ... ( N - 1 ) ) ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) )

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
  assert |- ( ph -> ( F ` M ) <_ ( F ` N ) )

  proof
    wph
    cN
    cM
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
    cle
    wbr
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    monoord.1
    cM
    cN
    eluzfz2
    syl
    @6
    wph
    @1
    @4
    wi
    #
    monoord.1
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @8
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    cM
    @0
    wcel
    #
    @2
    @2
    cle
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
    @0
    wcel
    #
    @2
    @17
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    @17
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @2
    @22
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    wi
    wph
    @7
    wi
    vx
    vn
    cM
    cN
    @8
    cM
    wceq
    #
    @12
    @15
    wph
    @27
    @9
    @13
    @11
    @14
    @8
    cM
    @0
    eleq1
    @27
    @10
    @2
    @2
    cle
    @8
    cM
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @8
    @17
    wceq
    #
    @12
    @21
    wph
    @28
    @9
    @18
    @11
    @20
    @8
    @17
    @0
    eleq1
    @28
    @10
    @19
    @2
    cle
    @8
    @17
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @8
    @22
    wceq
    #
    @12
    @26
    wph
    @29
    @9
    @23
    @11
    @25
    @8
    @22
    @0
    eleq1
    @29
    @10
    @24
    @2
    cle
    @8
    @22
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @8
    cN
    wceq
    #
    @12
    @7
    wph
    @30
    @9
    @1
    @11
    @4
    @8
    cN
    @0
    eleq1
    @30
    @10
    @3
    @2
    cle
    @8
    cN
    cF
    fveq2
    breq2d
    imbi12d
    imbi2d
    @16
    cM
    cz
    wcel
    wph
    @14
    @13
    wph
    @2
    wph
    @13
    vk
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    vk
    @0
    wral
    #
    @2
    cr
    wcel
    #
    wph
    @6
    @13
    monoord.1
    cM
    cN
    eluzfz1
    syl
    wph
    @33
    vk
    @0
    monoord.2
    ralrimiva
    #
    @33
    @35
    vk
    cM
    @0
    @31
    cM
    wceq
    @32
    @2
    cr
    @31
    cM
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    #
    leidd
    a1d
    a1i
    @17
    @5
    wcel
    #
    wph
    @21
    @26
    wph
    @38
    @21
    @26
    wi
    wph
    @38
    wa
    #
    @21
    @23
    @20
    wi
    @26
    @39
    @23
    @18
    @20
    wph
    @38
    @23
    @18
    wph
    @38
    @23
    wa
    #
    wa
    #
    @38
    @23
    @18
    wph
    @38
    @23
    simprl
    #
    wph
    @38
    @23
    simprr
    #
    @17
    cM
    cN
    peano2fzr
    syl2anc
    #
    expr
    imim1d
    @39
    @23
    @20
    @25
    wph
    @38
    @23
    @20
    @25
    wi
    @41
    @20
    @19
    @24
    cle
    wbr
    #
    @25
    @41
    @17
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
    @32
    @31
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vk
    @47
    wral
    #
    @45
    @41
    @38
    @46
    @17
    cuz
    cfv
    wcel
    #
    @48
    @42
    @41
    @17
    cz
    wcel
    #
    cN
    @22
    cuz
    cfv
    wcel
    #
    @53
    @41
    @38
    @54
    @42
    cM
    @17
    eluzelz
    syl
    @41
    @23
    @55
    @43
    @22
    cM
    cN
    elfzuz3
    syl
    @17
    cN
    eluzp1m1
    syl2anc
    @17
    cM
    @46
    elfzuzb
    sylanbrc
    wph
    @52
    @40
    wph
    @51
    vk
    @47
    monoord.3
    ralrimiva
    adantr
    @51
    @45
    vk
    @17
    @47
    @31
    @17
    wceq
    #
    @32
    @19
    @50
    @24
    cle
    @31
    @17
    cF
    fveq2
    #
    @56
    @49
    @22
    cF
    @31
    @17
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspcv
    sylc
    @41
    @35
    @19
    cr
    wcel
    #
    @24
    cr
    wcel
    #
    @20
    @45
    wa
    @25
    wi
    wph
    @35
    @40
    @37
    adantr
    @41
    @18
    @34
    @58
    @44
    wph
    @34
    @40
    @36
    adantr
    #
    @33
    @58
    vk
    @17
    @0
    @56
    @32
    @19
    cr
    @57
    eleq1d
    rspcv
    sylc
    @41
    @23
    @34
    @59
    @43
    @60
    @33
    @59
    vk
    @22
    @0
    @31
    @22
    wceq
    @32
    @24
    cr
    @31
    @22
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    @2
    @19
    @24
    letr
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
