include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wn.mm"
include "cli.mm"
include "cdm.mm"
include "crn.mm"
include "csup.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wss.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "caddc.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "simpr.mm"
include "breq1d.mm"
include "rexbii.mm"
include "climsup.mm"
include "cvv.mm"
include "nnex.mm"
include "fex.mm"
include "ltso.mm"
include "supex.mm"
include "a1i.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "syldan.mm"
include "mtand.mm"
include "ralnex.mm"
include "sylibr.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "ltnled.mm"
include "rexbidva.mm"
include "rexnal.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "mpbird.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "uznnssnn.mm"
include "ad3antlr.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "simp-4l.mm"
include "simpllr.mm"
include "cfz.mm"
include "fzssnn.mm"
include "cmin.mm"
include "simplll.mm"
include "syl2anc.mm"
include "monoord.mm"
include "syl21anc.mm"
include "ltletrd.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem lmdvg
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vl: setvar l
  assume lmdvg.1: |- ( ph -> F : NN --> ( 0 [,) +oo ) )
  assume lmdvg.2: |- ( ( ph /\ k e. NN ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) )
  assume lmdvg.3: |- ( ph -> -. F e. dom ~~> )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint j l
  disjoint k l
  disjoint l x
  disjoint F l
  disjoint l ph
  assert |- ( ph -> A. x e. RR E. j e. NN A. k e. ( ZZ>= ` j ) x < ( F ` k ) )

  proof
    wph
    vx
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
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
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @0
    @4
    cF
    cfv
    #
    clt
    wbr
    #
    vj
    cn
    wrex
    #
    @7
    wph
    @12
    vx
    cr
    wph
    @12
    vx
    cr
    wral
    @10
    @0
    cle
    wbr
    #
    vj
    cn
    wral
    #
    wn
    #
    vx
    cr
    wral
    #
    wph
    @14
    vx
    cr
    wrex
    #
    wn
    @16
    wph
    @17
    cF
    cli
    cdm
    wcel
    #
    lmdvg.3
    wph
    @17
    cF
    cF
    crn
    #
    cr
    clt
    csup
    #
    cli
    wbr
    #
    @18
    wph
    @17
    wa
    #
    vx
    vl
    cF
    c1
    cn
    nnuz
    @22
    1zzd
    wph
    cn
    cr
    cF
    wf
    #
    @17
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    @24
    cr
    wss
    @23
    lmdvg.1
    rge0ssre
    cn
    @24
    cr
    cF
    fss
    sylancl
    #
    adantr
    wph
    vl
    cv
    #
    cn
    wcel
    #
    @27
    cF
    cfv
    #
    @27
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
    @17
    wph
    @32
    vl
    cn
    wph
    @2
    @1
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
    cn
    wral
    @32
    vl
    cn
    wral
    wph
    @35
    vk
    cn
    lmdvg.2
    ralrimiva
    @35
    @32
    vk
    vl
    cn
    @1
    @27
    wceq
    #
    @2
    @29
    @34
    @31
    cle
    @1
    @27
    cF
    fveq2
    @36
    @33
    @30
    cF
    @1
    @27
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    cbvralv
    sylib
    r19.21bi
    #
    adantlr
    @22
    @17
    @29
    @0
    cle
    wbr
    #
    vl
    cn
    wral
    #
    vx
    cr
    wrex
    wph
    @17
    simpr
    @14
    @39
    vx
    cr
    @13
    @38
    vj
    vl
    cn
    @4
    @27
    wceq
    @10
    @29
    @0
    cle
    @4
    @27
    cF
    fveq2
    breq1d
    cbvralv
    rexbii
    sylib
    climsup
    wph
    @21
    wa
    #
    cF
    cvv
    wcel
    #
    @20
    cvv
    wcel
    #
    @21
    @18
    wph
    @41
    @21
    wph
    @25
    cn
    cvv
    wcel
    @41
    lmdvg.1
    nnex
    cn
    @24
    cvv
    cF
    fex
    sylancl
    adantr
    @42
    @40
    cr
    @19
    clt
    ltso
    supex
    a1i
    wph
    @21
    simpr
    cF
    @20
    cvv
    cvv
    cli
    breldmg
    syl3anc
    syldan
    mtand
    @14
    vx
    cr
    ralnex
    sylibr
    wph
    @12
    @15
    vx
    cr
    @9
    @12
    @13
    wn
    #
    vj
    cn
    wrex
    @15
    @9
    @11
    @43
    vj
    cn
    @9
    @4
    cn
    wcel
    #
    wa
    #
    @0
    @10
    wph
    @8
    @44
    simplr
    #
    @9
    cn
    cr
    @4
    cF
    wph
    @23
    @8
    @26
    adantr
    #
    ffvelrnda
    #
    ltnled
    rexbidva
    @13
    vj
    cn
    rexnal
    syl6bb
    ralbidva
    mpbird
    r19.21bi
    @9
    @11
    @6
    vj
    cn
    @45
    @11
    @6
    @45
    @11
    wa
    #
    @3
    vk
    @5
    @49
    @1
    @5
    wcel
    #
    wa
    #
    @0
    @10
    @2
    @45
    @8
    @11
    @50
    @46
    ad2antrr
    @45
    @10
    cr
    wcel
    @11
    @50
    @48
    ad2antrr
    @51
    cn
    cr
    @1
    cF
    @9
    @23
    @44
    @11
    @50
    @47
    ad3antrrr
    @51
    @5
    cn
    @1
    @44
    @5
    cn
    wss
    @9
    @11
    @50
    @4
    uznnssnn
    ad3antlr
    @49
    @50
    simpr
    #
    sseldd
    ffvelrnd
    @45
    @11
    @50
    simplr
    @51
    wph
    @44
    @50
    @10
    @2
    cle
    wbr
    wph
    @8
    @44
    @11
    @50
    simp-4l
    @9
    @44
    @11
    @50
    simpllr
    @52
    wph
    @44
    wa
    #
    @50
    wa
    #
    vl
    cF
    @4
    @1
    @53
    @50
    simpr
    @54
    @27
    @4
    @1
    cfz
    co
    #
    wcel
    #
    wa
    #
    cn
    cr
    @27
    cF
    wph
    @23
    @44
    @50
    @56
    @26
    ad3antrrr
    @57
    @55
    cn
    @27
    @44
    @55
    cn
    wss
    wph
    @50
    @56
    @4
    @1
    fzssnn
    ad3antlr
    @54
    @56
    simpr
    sseldd
    ffvelrnd
    @54
    @27
    @4
    @1
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
    wph
    @28
    @32
    wph
    @44
    @50
    @60
    simplll
    @61
    @59
    cn
    @27
    @44
    @59
    cn
    wss
    wph
    @50
    @60
    @4
    @58
    fzssnn
    ad3antlr
    @54
    @60
    simpr
    sseldd
    @37
    syl2anc
    monoord
    syl21anc
    ltletrd
    ralrimiva
    ex
    reximdva
    mpd
    ralrimiva
end
