include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "xnegcld.mm"
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
include "wb.mm"
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
include "xleneg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "xnegeqd.mm"
include "xnegex.mm"
include "fvmpt.mm"
include "3brtr4d.mm"
include "monoordxrv.mm"
include "eluzfz1.mm"
include "eluzfz2.mm"
include "3brtr3d.mm"
include "mpbird.mm"

theorem monoord2xrv
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume monoord2xrv.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume monoord2xrv.x: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR* )
  assume monoord2xrv.l: |- ( ( ph /\ k e. ( M ... ( N - 1 ) ) ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )

  disjoint F k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint F n
  disjoint k n
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
    #
    @1
    cxne
    #
    @0
    cxne
    #
    cle
    wbr
    #
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
    cxne
    #
    cmpt
    #
    cfv
    #
    cN
    @10
    cfv
    #
    @3
    @4
    cle
    wph
    vn
    @10
    cM
    cN
    monoord2xrv.n
    wph
    @6
    cxr
    vn
    cv
    #
    @10
    wph
    vk
    @6
    @9
    cxr
    @10
    wph
    @7
    @6
    wcel
    wa
    @8
    monoord2xrv.x
    xnegcld
    @10
    eqid
    #
    fmptd
    ffvelrnda
    wph
    @13
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
    @13
    cF
    cfv
    #
    cxne
    #
    @13
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cxne
    #
    @13
    @10
    cfv
    #
    @21
    @10
    cfv
    #
    cle
    @18
    @22
    @19
    cle
    wbr
    #
    @20
    @23
    cle
    wbr
    #
    wph
    @26
    vn
    @16
    wph
    @7
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @8
    cle
    wbr
    #
    vk
    @16
    wral
    @26
    vn
    @16
    wral
    wph
    @30
    vk
    @16
    monoord2xrv.l
    ralrimiva
    @30
    @26
    vk
    vn
    @16
    @7
    @13
    wceq
    #
    @29
    @22
    @8
    @19
    cle
    @31
    @28
    @21
    cF
    @7
    @13
    c1
    caddc
    oveq1
    fveq2d
    @7
    @13
    cF
    fveq2
    #
    breq12d
    cbvralv
    sylib
    r19.21bi
    @18
    @22
    cxr
    wcel
    #
    @19
    cxr
    wcel
    #
    @26
    @27
    wb
    @18
    @21
    @6
    wcel
    #
    @8
    cxr
    wcel
    #
    vk
    @6
    wral
    #
    @33
    @18
    @21
    cM
    @15
    c1
    caddc
    co
    #
    cfz
    co
    #
    @6
    @17
    @21
    @39
    wcel
    wph
    @13
    cM
    @15
    fzp1elp1
    adantl
    wph
    @39
    @6
    wceq
    @17
    wph
    @38
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
    @38
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
    monoord2xrv.n
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
    @37
    @17
    wph
    @36
    vk
    @6
    monoord2xrv.x
    ralrimiva
    #
    adantr
    #
    @36
    @33
    vk
    @21
    @6
    @7
    @21
    wceq
    #
    @8
    @22
    cxr
    @7
    @21
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    @18
    @13
    @6
    wcel
    #
    @37
    @34
    wph
    @16
    @6
    @13
    wph
    @39
    @16
    @6
    cM
    @15
    fzssp1
    @41
    syl5sseq
    sselda
    #
    @44
    @36
    @34
    vk
    @13
    @6
    @31
    @8
    @19
    cxr
    @32
    eleq1d
    rspcv
    sylc
    @22
    @19
    xleneg
    syl2anc
    mpbid
    @18
    @47
    @24
    @20
    wceq
    @48
    vk
    @13
    @9
    @20
    @6
    @10
    @31
    @8
    @19
    @32
    xnegeqd
    @14
    @19
    xnegex
    fvmpt
    syl
    @18
    @35
    @25
    @23
    wceq
    @42
    vk
    @21
    @9
    @23
    @6
    @10
    @45
    @8
    @22
    @46
    xnegeqd
    @14
    @22
    xnegex
    fvmpt
    syl
    3brtr4d
    monoordxrv
    wph
    cM
    @6
    wcel
    #
    @11
    @3
    wceq
    wph
    @40
    @49
    monoord2xrv.n
    cM
    cN
    eluzfz1
    syl
    #
    vk
    cM
    @9
    @3
    @6
    @10
    @7
    cM
    wceq
    #
    @8
    @1
    @7
    cM
    cF
    fveq2
    #
    xnegeqd
    @14
    @1
    xnegex
    fvmpt
    syl
    wph
    cN
    @6
    wcel
    #
    @12
    @4
    wceq
    wph
    @40
    @53
    monoord2xrv.n
    cM
    cN
    eluzfz2
    syl
    #
    vk
    cN
    @9
    @4
    @6
    @10
    @7
    cN
    wceq
    #
    @8
    @0
    @7
    cN
    cF
    fveq2
    #
    xnegeqd
    @14
    @0
    xnegex
    fvmpt
    syl
    3brtr3d
    wph
    @0
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    @2
    @5
    wb
    wph
    @53
    @37
    @57
    @54
    @43
    @36
    @57
    vk
    cN
    @6
    @55
    @8
    @0
    cxr
    @56
    eleq1d
    rspcv
    sylc
    wph
    @49
    @37
    @58
    @50
    @43
    @36
    @58
    vk
    cM
    @6
    @51
    @8
    @1
    cxr
    @52
    eleq1d
    rspcv
    sylc
    @0
    @1
    xleneg
    syl2anc
    mpbird
end
