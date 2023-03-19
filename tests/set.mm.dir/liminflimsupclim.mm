include "cli.mm"
include "wrel.mm"
include "clsp.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "climrel.mm"
include "a1i.mm"
include "cc.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "clsi.mm"
include "cr.mm"
include "cvv.mm"
include "fvexi.mm"
include "fexd.mm"
include "limsupcld.mm"
include "rexrd.mm"
include "frexr.mm"
include "liminflelimsupuz.mm"
include "xrletrid.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "cneg.mm"
include "caddc.mm"
include "nfcv.mm"
include "cz.mm"
include "adantr.mm"
include "wf.mm"
include "simpr.mm"
include "liminflt.mm"
include "ad2antrr.mm"
include "uztrn2.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "adantllr.mm"
include "rpre.mm"
include "syl.mm"
include "ltsubadd2d.mm"
include "bicomd.mm"
include "wb.mm"
include "eqcomd.mm"
include "negsubdi2d.mm"
include "breq1d.mm"
include "resubcld.mm"
include "ltnegcon1.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "ad3antrrr.mm"
include "3bitrd.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "limsupgt.mm"
include "ltsub23.mm"
include "syl3anc.mm"
include "jca.mm"
include "rexanuz2.mm"
include "sylibr.mm"
include "wi.mm"
include "simplll.mm"
include "simpllr.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "ad2antlr.mm"
include "abslt.mm"
include "mpbird.mm"
include "ex.mm"
include "syl21anc.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fssd.mm"
include "climuz.mm"
include "releldm.mm"

theorem liminflimsupclim
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume liminflimsupclim.1: |- ( ph -> M e. ZZ )
  assume liminflimsupclim.2: |- Z = ( ZZ>= ` M )
  assume liminflimsupclim.3: |- ( ph -> F : Z --> RR )
  assume liminflimsupclim.4: |- ( ph -> ( liminf ` F ) e. RR )
  assume liminflimsupclim.5: |- ( ph -> ( limsup ` F ) <_ ( liminf ` F ) )


  assert |- ( ph -> F e. dom ~~> )

  proof
    wph
    cli
    wrel
    #
    cF
    cF
    clsp
    cfv
    #
    cli
    wbr
    #
    cF
    cli
    cdm
    wcel
    @0
    wph
    climrel
    a1i
    wph
    @2
    @1
    cc
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @1
    cmin
    co
    #
    cabs
    cfv
    vx
    cv
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
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    wph
    @3
    @13
    wph
    @1
    wph
    @1
    cF
    clsi
    cfv
    #
    cr
    wph
    @1
    @14
    wph
    cF
    cvv
    wph
    cZ
    cr
    cvv
    cF
    liminflimsupclim.3
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    liminflimsupclim.2
    fvexi
    a1i
    fexd
    limsupcld
    wph
    @14
    liminflimsupclim.4
    rexrd
    liminflimsupclim.5
    wph
    cF
    cM
    cZ
    liminflimsupclim.1
    liminflimsupclim.2
    wph
    cZ
    cF
    liminflimsupclim.3
    frexr
    liminflelimsupuz
    xrletrid
    #
    liminflimsupclim.4
    eqeltrd
    #
    recnd
    #
    wph
    @12
    vx
    crp
    wph
    @7
    crp
    wcel
    #
    wa
    #
    @7
    cneg
    #
    @6
    clt
    wbr
    #
    @6
    @7
    clt
    wbr
    #
    wa
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    #
    @12
    @19
    @21
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    #
    @22
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    #
    wa
    @25
    @19
    @27
    @29
    @19
    @14
    @5
    @7
    caddc
    co
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    @27
    @19
    vj
    vk
    cF
    cM
    @7
    cZ
    vk
    cF
    nfcv
    #
    wph
    cM
    cz
    wcel
    @18
    liminflimsupclim.1
    adantr
    #
    liminflimsupclim.2
    wph
    cZ
    cr
    cF
    wf
    #
    @18
    liminflimsupclim.3
    adantr
    #
    wph
    @14
    cr
    wcel
    #
    @18
    liminflimsupclim.4
    adantr
    #
    wph
    @18
    simpr
    #
    liminflt
    @19
    @31
    @26
    vj
    cZ
    @19
    @9
    cZ
    wcel
    #
    wa
    #
    @30
    @21
    vk
    @10
    @40
    @4
    @10
    wcel
    #
    wa
    #
    @30
    @14
    @5
    cmin
    co
    #
    @7
    clt
    wbr
    #
    @20
    @5
    @14
    cmin
    co
    #
    clt
    wbr
    #
    @21
    @42
    @44
    @30
    @42
    @14
    @5
    @7
    @19
    @36
    @39
    @41
    @37
    ad2antrr
    #
    wph
    @39
    @41
    @5
    cr
    wcel
    #
    @18
    wph
    @39
    wa
    @41
    wa
    #
    cZ
    cr
    @4
    cF
    wph
    @34
    @39
    @41
    liminflimsupclim.3
    ad2antrr
    @39
    @41
    @4
    cZ
    wcel
    #
    wph
    cM
    @4
    @9
    cZ
    liminflimsupclim.2
    uztrn2
    #
    adantll
    ffvelrnd
    #
    adantllr
    #
    @42
    @18
    @7
    cr
    wcel
    #
    @19
    @18
    @39
    @41
    @38
    ad2antrr
    @7
    rpre
    #
    syl
    #
    ltsubadd2d
    bicomd
    @42
    @44
    @45
    cneg
    #
    @7
    clt
    wbr
    #
    @46
    @42
    @58
    @44
    wph
    @39
    @41
    @58
    @44
    wb
    @18
    @49
    @57
    @43
    @7
    clt
    @49
    @5
    @14
    @49
    @5
    @52
    recnd
    wph
    @14
    cc
    wcel
    @39
    @41
    wph
    @14
    @1
    cc
    wph
    @1
    @14
    @15
    eqcomd
    #
    @17
    eqeltrd
    ad2antrr
    negsubdi2d
    breq1d
    adantllr
    bicomd
    @42
    @45
    cr
    wcel
    @54
    @58
    @46
    wb
    @42
    @5
    @14
    @53
    @47
    resubcld
    @56
    @45
    @7
    ltnegcon1
    syl2anc
    bitrd
    wph
    @46
    @21
    wb
    @18
    @39
    @41
    wph
    @45
    @6
    @20
    clt
    wph
    @14
    @1
    @5
    cmin
    @59
    oveq2d
    breq2d
    ad3antrrr
    3bitrd
    ralbidva
    rexbidva
    mpbid
    @19
    @5
    @7
    cmin
    co
    @1
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    @29
    @19
    vj
    vk
    cF
    cM
    @7
    cZ
    @32
    @33
    liminflimsupclim.2
    @35
    wph
    @1
    cr
    wcel
    #
    @18
    @16
    adantr
    #
    @38
    limsupgt
    @19
    @61
    @28
    vj
    cZ
    @40
    @60
    @22
    vk
    @10
    @42
    @48
    @54
    @62
    @60
    @22
    wb
    @53
    @56
    @19
    @62
    @39
    @41
    @63
    ad2antrr
    @5
    @7
    @1
    ltsub23
    syl3anc
    ralbidva
    rexbidva
    mpbid
    jca
    @21
    @22
    vj
    vk
    cM
    cZ
    liminflimsupclim.2
    rexanuz2
    sylibr
    @19
    @24
    @11
    vj
    cZ
    @40
    @23
    @8
    vk
    @10
    @42
    wph
    @18
    @50
    @23
    @8
    wi
    wph
    @18
    @39
    @41
    simplll
    wph
    @18
    @39
    @41
    simpllr
    @39
    @41
    @50
    @19
    @51
    adantll
    @19
    @50
    wa
    #
    @23
    @8
    @64
    @23
    wa
    @8
    @23
    @64
    @23
    simpr
    @64
    @8
    @23
    wb
    #
    @23
    @64
    @6
    cr
    wcel
    #
    @54
    @65
    wph
    @50
    @66
    @18
    wph
    @50
    wa
    @5
    @1
    wph
    cZ
    cr
    @4
    cF
    liminflimsupclim.3
    ffvelrnda
    wph
    @62
    @50
    @16
    adantr
    resubcld
    adantlr
    @18
    @54
    wph
    @50
    @55
    ad2antlr
    @6
    @7
    abslt
    syl2anc
    adantr
    mpbird
    ex
    syl21anc
    ralimdva
    reximdva
    mpd
    ralrimiva
    jca
    wph
    vx
    @1
    vj
    vk
    cF
    cM
    cZ
    @32
    liminflimsupclim.1
    liminflimsupclim.2
    wph
    cZ
    cr
    cc
    cF
    liminflimsupclim.3
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    climuz
    mpbird
    cF
    @1
    cli
    releldm
    syl2anc
end
