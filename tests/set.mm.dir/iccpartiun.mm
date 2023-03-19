include "cc0.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "cfzo.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "ciccp.mm"
include "wi.mm"
include "cn.mm"
include "wral.mm"
include "iccelpart.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "expcom.mm"
include "3syl.mm"
include "mpd.mm"
include "wa.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "cn0.mm"
include "cfz.mm"
include "nnnn0.mm"
include "0elfz.mm"
include "iccpartxr.mm"
include "nn0fz0.mm"
include "biimpi.mm"
include "jca.mm"
include "adantr.mm"
include "elfzofz.mm"
include "iccpartgel.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "syl2anr.mm"
include "fzofzp1.mm"
include "iccpartleu.mm"
include "breq1d.mm"
include "icossico.mm"
include "syl12anc.mm"
include "sseld.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem iccpartiun
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let vp: setvar p
  let cX: class X
  let vx: setvar x
  assume iccpartiun.m: |- ( ph -> M e. NN )
  assume iccpartiun.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M i
  disjoint P i
  disjoint i ph
  disjoint M j
  disjoint M k
  disjoint M p
  disjoint i j
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint k p
  disjoint P j
  disjoint P k
  disjoint P p
  disjoint X i
  disjoint X p
  disjoint M x
  disjoint i x
  disjoint p x
  disjoint P x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( P ` 0 ) [,) ( P ` M ) ) = U_ i e. ( 0 ..^ M ) ( ( P ` i ) [,) ( P ` ( i + 1 ) ) ) )

  proof
    wph
    vx
    cc0
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    cico
    co
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    vi
    cv
    #
    cP
    cfv
    #
    @4
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cico
    co
    #
    ciun
    #
    wph
    vx
    cv
    #
    @2
    wcel
    #
    @10
    @8
    wcel
    #
    vi
    @3
    wrex
    #
    @10
    @9
    wcel
    wph
    @11
    @13
    wph
    cP
    cM
    ciccp
    cfv
    #
    wcel
    #
    @11
    @13
    wi
    #
    iccpartiun.p
    wph
    cM
    cn
    wcel
    #
    @10
    cc0
    vp
    cv
    #
    cfv
    #
    cM
    @18
    cfv
    #
    cico
    co
    #
    wcel
    #
    @10
    @4
    @18
    cfv
    #
    @6
    @18
    cfv
    #
    cico
    co
    #
    wcel
    #
    vi
    @3
    wrex
    #
    wi
    #
    vp
    @14
    wral
    #
    @15
    @16
    wi
    iccpartiun.m
    vi
    cM
    @10
    vp
    iccelpart
    @15
    @29
    @16
    @28
    @16
    vp
    cP
    @14
    @18
    cP
    wceq
    #
    @22
    @11
    @27
    @13
    @30
    @21
    @2
    @10
    @30
    @19
    @0
    @20
    @1
    cico
    cc0
    @18
    cP
    fveq1
    cM
    @18
    cP
    fveq1
    oveq12d
    eleq2d
    @30
    @26
    @12
    vi
    @3
    @30
    @25
    @8
    @10
    @30
    @23
    @5
    @24
    @7
    cico
    @4
    @18
    cP
    fveq1
    @6
    @18
    cP
    fveq1
    oveq12d
    eleq2d
    rexbidv
    imbi12d
    rspcva
    expcom
    3syl
    mpd
    wph
    @12
    @11
    vi
    @3
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @8
    @2
    @10
    @32
    @0
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    wa
    #
    @0
    @5
    cle
    wbr
    #
    @7
    @1
    cle
    wbr
    #
    @8
    @2
    wss
    wph
    @35
    @31
    wph
    @33
    @34
    wph
    cP
    cc0
    cM
    iccpartiun.m
    iccpartiun.p
    wph
    @17
    cM
    cn0
    wcel
    #
    cc0
    cc0
    cM
    cfz
    co
    #
    wcel
    iccpartiun.m
    cM
    nnnn0
    #
    cM
    0elfz
    3syl
    iccpartxr
    wph
    cP
    cM
    cM
    iccpartiun.m
    iccpartiun.p
    wph
    @17
    @38
    cM
    @39
    wcel
    #
    iccpartiun.m
    @40
    @38
    @41
    cM
    nn0fz0
    biimpi
    3syl
    iccpartxr
    jca
    adantr
    @31
    @4
    @39
    wcel
    @0
    vj
    cv
    #
    cP
    cfv
    #
    cle
    wbr
    #
    vj
    @39
    wral
    @36
    wph
    @4
    cc0
    cM
    elfzofz
    wph
    cP
    vj
    cM
    iccpartiun.m
    iccpartiun.p
    iccpartgel
    @44
    @36
    vj
    @4
    @39
    vj
    vi
    weq
    @43
    @5
    @0
    cle
    @42
    @4
    cP
    fveq2
    breq2d
    rspcva
    syl2anr
    @31
    @6
    @39
    wcel
    vk
    cv
    #
    cP
    cfv
    #
    @1
    cle
    wbr
    #
    vk
    @39
    wral
    @37
    wph
    cc0
    cM
    @4
    fzofzp1
    wph
    cP
    vk
    cM
    iccpartiun.m
    iccpartiun.p
    iccpartleu
    @47
    @37
    vk
    @6
    @39
    @45
    @6
    wceq
    @46
    @7
    @1
    cle
    @45
    @6
    cP
    fveq2
    breq1d
    rspcva
    syl2anr
    @0
    @1
    @5
    @7
    icossico
    syl12anc
    sseld
    rexlimdva
    impbid
    vi
    @10
    @3
    @8
    eliun
    syl6bbr
    eqrdv
end
