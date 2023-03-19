include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cz.mm"
include "cdm.mm"
include "wcel.mm"
include "cpnf.mm"
include "cioc.mm"
include "co.mm"
include "wa.mm"
include "cordt.mm"
include "wi.mm"
include "iocpnfordt.mm"
include "a1i.mm"
include "cxr.mm"
include "cc.mm"
include "cpm.mm"
include "clm.mm"
include "w3a.mm"
include "clsxlim.mm"
include "df-xlim.mm"
include "breqi.mm"
include "sylib.mm"
include "nfcv.mm"
include "ctopon.mm"
include "letopon.mm"
include "lmbr3.mm"
include "mpbid.mm"
include "simp3d.mm"
include "jca.mm"
include "clt.mm"
include "rexrd.mm"
include "simp2d.mm"
include "ltpnfd.mm"
include "ubioc1.mm"
include "syl3anc.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylc.mm"
include "nfv.mm"
include "adantr.mm"
include "ffdmd.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "simprr.mm"
include "iocgtlbd.mm"
include "xrltled.mm"
include "ex.mm"
include "ralimda.mm"
include "a1d.mm"
include "reximdai.mm"
include "mpd.mm"
include "wb.mm"
include "rexuz3.mm"
include "syl.mm"
include "mpbird.mm"

theorem xlimpnfvlem1
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vu: setvar u
  let vx: setvar x
  assume xlimpnfvlem1.m: |- ( ph -> M e. ZZ )
  assume xlimpnfvlem1.z: |- Z = ( ZZ>= ` M )
  assume xlimpnfvlem1.f: |- ( ph -> F : Z --> RR* )
  assume xlimpnfvlem1.c: |- ( ph -> F ~~>* +oo )
  assume xlimpnfvlem1.x: |- ( ph -> X e. RR )

  disjoint F j
  disjoint F k
  disjoint j k
  disjoint M j
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint k ph
  disjoint F u
  disjoint j u
  disjoint k u
  disjoint X u
  disjoint k x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) X <_ ( F ` k ) )

  proof
    wph
    cX
    vk
    cv
    #
    cF
    cfv
    #
    cle
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
    @5
    vj
    cz
    wrex
    #
    wph
    @0
    cF
    cdm
    #
    wcel
    #
    @1
    cX
    cpnf
    cioc
    co
    #
    wcel
    #
    wa
    #
    vk
    @4
    wral
    #
    vj
    cz
    wrex
    #
    @7
    wph
    @10
    cle
    cordt
    cfv
    #
    wcel
    #
    cpnf
    vu
    cv
    #
    wcel
    #
    @9
    @1
    @17
    wcel
    #
    wa
    #
    vk
    @4
    wral
    #
    vj
    cz
    wrex
    #
    wi
    #
    vu
    @15
    wral
    #
    wa
    cpnf
    @10
    wcel
    #
    @14
    wph
    @16
    @24
    @16
    wph
    cX
    iocpnfordt
    a1i
    wph
    cF
    cxr
    cc
    cpm
    co
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @24
    wph
    cF
    cpnf
    @15
    clm
    cfv
    #
    wbr
    #
    @26
    @27
    @24
    w3a
    wph
    cF
    cpnf
    clsxlim
    wbr
    @29
    xlimpnfvlem1.c
    cF
    cpnf
    clsxlim
    @28
    df-xlim
    breqi
    sylib
    wph
    vu
    cpnf
    vj
    vk
    cF
    @15
    cxr
    vk
    cF
    nfcv
    @15
    cxr
    ctopon
    cfv
    wcel
    wph
    letopon
    a1i
    lmbr3
    mpbid
    #
    simp3d
    jca
    wph
    cX
    cxr
    wcel
    #
    @27
    cX
    cpnf
    clt
    wbr
    @25
    wph
    cX
    xlimpnfvlem1.x
    rexrd
    #
    wph
    @26
    @27
    @24
    @30
    simp2d
    #
    wph
    cX
    xlimpnfvlem1.x
    ltpnfd
    cX
    cpnf
    ubioc1
    syl3anc
    @23
    @25
    @14
    wi
    vu
    @10
    @15
    @17
    @10
    wceq
    #
    @18
    @25
    @22
    @14
    @17
    @10
    cpnf
    eleq2
    @34
    @21
    @13
    vj
    cz
    @34
    @20
    @12
    vk
    @4
    @34
    @19
    @11
    @9
    @17
    @10
    @1
    eleq2
    anbi2d
    ralbidv
    rexbidv
    imbi12d
    rspcva
    sylc
    wph
    @13
    @5
    vj
    cz
    wph
    vj
    nfv
    wph
    @13
    @5
    wi
    @3
    cz
    wcel
    wph
    @12
    @2
    vk
    @4
    wph
    vk
    nfv
    wph
    @12
    @2
    wi
    @0
    @4
    wcel
    wph
    @12
    @2
    wph
    @12
    wa
    #
    cX
    @1
    wph
    @31
    @12
    @32
    adantr
    #
    wph
    @9
    @1
    cxr
    wcel
    @11
    wph
    @8
    cxr
    @0
    cF
    wph
    cZ
    cxr
    cF
    xlimpnfvlem1.f
    ffdmd
    ffvelrnda
    adantrr
    @35
    cX
    cpnf
    @1
    @36
    wph
    @27
    @12
    @33
    adantr
    wph
    @9
    @11
    simprr
    iocgtlbd
    xrltled
    ex
    adantr
    ralimda
    a1d
    reximdai
    mpd
    wph
    cM
    cz
    wcel
    @6
    @7
    wb
    xlimpnfvlem1.m
    @2
    vj
    vk
    cM
    cZ
    xlimpnfvlem1.z
    rexuz3
    syl
    mpbird
end
