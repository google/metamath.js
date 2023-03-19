include "cmnf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "clm.mm"
include "cxr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "cvv.mm"
include "wf.mm"
include "wss.mm"
include "ctopon.mm"
include "letopon.mm"
include "a1i.mm"
include "elfvexd.mm"
include "cnex.mm"
include "uzsscn2.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "mnfxr.mm"
include "cico.mm"
include "cr.mm"
include "mnfnei.mm"
include "adantll.mm"
include "clt.mm"
include "nfv.mm"
include "nfan.mm"
include "simprr.mm"
include "uztrn2.mm"
include "3adant1.mm"
include "wceq.mm"
include "fdmd.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "ad5ant134.mm"
include "adantl4r.mm"
include "simp-4r.mm"
include "rexr.mm"
include "syl.mm"
include "simp-4l.mm"
include "ad4ant23.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "mnfled.mm"
include "simpr.mm"
include "elicod.mm"
include "ad5ant1345.mm"
include "sseldd.mm"
include "jca.mm"
include "ex.mm"
include "ralimda.mm"
include "adantrr.mm"
include "mpd.mm"
include "3impb.mm"
include "r19.21bi.mm"
include "adantr.mm"
include "reximdd.mm"
include "wb.mm"
include "rexuz3.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "rexlimdva2.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "nfcv.mm"
include "lmbr3.mm"
include "mpbird.mm"
include "df-xlim.mm"
include "breqi.mm"

theorem xlimmnfvlem2
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vu: setvar u
  assume xlimmnfvlem2.k: |- F/ k ph
  assume xlimmnfvlem2.j: |- F/ j ph
  assume xlimmnfvlem2.m: |- ( ph -> M e. ZZ )
  assume xlimmnfvlem2.z: |- Z = ( ZZ>= ` M )
  assume xlimmnfvlem2.f: |- ( ph -> F : Z --> RR* )
  assume xlimmnfvlem2.g: |- ( ph -> A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) < x )

  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint ph x
  disjoint k x
  disjoint F u
  disjoint j u
  disjoint k u
  disjoint u x
  disjoint ph u
  assert |- ( ph -> F ~~>* -oo )

  proof
    wph
    cF
    cmnf
    clsxlim
    wbr
    #
    cF
    cmnf
    cle
    cordt
    cfv
    #
    clm
    cfv
    #
    wbr
    #
    wph
    @3
    cF
    cxr
    cc
    cpm
    co
    wcel
    #
    cmnf
    cxr
    wcel
    #
    cmnf
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @8
    cF
    cfv
    #
    @6
    wcel
    #
    wa
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
    cz
    wrex
    #
    wi
    #
    vu
    @1
    wral
    #
    w3a
    wph
    @4
    @5
    @19
    wph
    cxr
    cvv
    wcel
    cc
    cvv
    wcel
    #
    cZ
    cxr
    cF
    wf
    cZ
    cc
    wss
    #
    @4
    wph
    @1
    ctopon
    cxr
    @1
    cxr
    ctopon
    cfv
    wcel
    wph
    letopon
    a1i
    #
    elfvexd
    @20
    wph
    cnex
    a1i
    xlimmnfvlem2.f
    @21
    wph
    cM
    cZ
    xlimmnfvlem2.z
    uzsscn2
    a1i
    cxr
    cc
    cZ
    cF
    cvv
    cvv
    elpm2r
    syl22anc
    @5
    wph
    mnfxr
    a1i
    wph
    @18
    vu
    @1
    wph
    @6
    @1
    wcel
    #
    wa
    #
    @7
    @17
    @24
    @7
    wa
    cmnf
    vx
    cv
    #
    cico
    co
    #
    @6
    wss
    #
    vx
    cr
    wrex
    #
    @17
    @23
    @7
    @28
    wph
    vx
    @6
    mnfnei
    adantll
    wph
    @28
    @17
    wi
    @23
    @7
    wph
    @27
    @17
    vx
    cr
    wph
    @25
    cr
    wcel
    #
    wa
    #
    @27
    wa
    #
    @16
    vj
    cZ
    wrex
    #
    @17
    @31
    @11
    @25
    clt
    wbr
    #
    vk
    @15
    wral
    #
    @16
    vj
    cZ
    @30
    @27
    vj
    wph
    @29
    vj
    xlimmnfvlem2.j
    @29
    vj
    nfv
    nfan
    @27
    vj
    nfv
    nfan
    @31
    @14
    cZ
    wcel
    #
    @34
    @16
    @31
    @35
    @34
    wa
    wa
    @34
    @16
    @31
    @35
    @34
    simprr
    @31
    @35
    @34
    @16
    wi
    @34
    @31
    @35
    wa
    #
    @33
    @13
    vk
    @15
    @31
    @35
    vk
    @30
    @27
    vk
    wph
    @29
    vk
    xlimmnfvlem2.k
    @29
    vk
    nfv
    nfan
    @27
    vk
    nfv
    nfan
    @35
    vk
    nfv
    nfan
    @36
    @8
    @15
    wcel
    #
    wa
    #
    @33
    @13
    @38
    @33
    wa
    #
    @10
    @12
    wph
    @29
    @27
    @35
    @37
    @33
    @10
    wph
    @35
    @37
    @10
    @27
    @33
    wph
    @35
    @37
    w3a
    @8
    cZ
    @9
    @35
    @37
    @8
    cZ
    wcel
    #
    wph
    cM
    @8
    @14
    cZ
    xlimmnfvlem2.z
    uztrn2
    #
    3adant1
    wph
    @35
    @9
    cZ
    wceq
    @37
    wph
    cZ
    cxr
    cF
    xlimmnfvlem2.f
    fdmd
    3ad2ant1
    eleqtrrd
    ad5ant134
    adantl4r
    @39
    @26
    @6
    @11
    wph
    @29
    @27
    @35
    @37
    @33
    @27
    wph
    @27
    @35
    @37
    @33
    simp-4r
    adantl4r
    @30
    @35
    @37
    @33
    @11
    @26
    wcel
    @27
    @30
    @35
    wa
    @37
    wa
    #
    @33
    wa
    #
    cmnf
    @25
    @11
    @5
    @43
    mnfxr
    a1i
    @43
    @29
    @25
    cxr
    wcel
    wph
    @29
    @35
    @37
    @33
    simp-4r
    @25
    rexr
    syl
    @43
    wph
    @40
    @11
    cxr
    wcel
    wph
    @29
    @35
    @37
    @33
    simp-4l
    @35
    @37
    @40
    @30
    @33
    @41
    ad4ant23
    wph
    cZ
    cxr
    @8
    cF
    xlimmnfvlem2.f
    ffvelrnda
    syl2anc
    #
    @43
    @11
    @44
    mnfled
    @42
    @33
    simpr
    elicod
    ad5ant1345
    sseldd
    jca
    ex
    ralimda
    adantrr
    mpd
    3impb
    @30
    @34
    vj
    cZ
    wrex
    #
    @27
    wph
    @45
    vx
    cr
    xlimmnfvlem2.g
    r19.21bi
    adantr
    reximdd
    wph
    @32
    @17
    wb
    #
    @29
    @27
    wph
    cM
    cz
    wcel
    @46
    xlimmnfvlem2.m
    @13
    vj
    vk
    cM
    cZ
    xlimmnfvlem2.z
    rexuz3
    syl
    ad2antrr
    mpbid
    rexlimdva2
    ad2antrr
    mpd
    ex
    ralrimiva
    3jca
    wph
    vu
    cmnf
    vj
    vk
    cF
    @1
    cxr
    vk
    cF
    nfcv
    @22
    lmbr3
    mpbird
    @0
    @3
    wb
    wph
    cF
    cmnf
    clsxlim
    @2
    df-xlim
    breqi
    a1i
    mpbird
end
