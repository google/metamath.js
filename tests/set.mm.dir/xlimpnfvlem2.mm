include "cpnf.mm"
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
include "pnfxr.mm"
include "cioc.mm"
include "cr.mm"
include "pnfnei.mm"
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
include "simpr.mm"
include "ffvelrnd.mm"
include "pnfged.mm"
include "eliocd.mm"
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

theorem xlimpnfvlem2
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vu: setvar u
  assume xlimpnfvlem2.k: |- F/ k ph
  assume xlimpnfvlem2.j: |- F/ j ph
  assume xlimpnfvlem2.m: |- ( ph -> M e. ZZ )
  assume xlimpnfvlem2.z: |- Z = ( ZZ>= ` M )
  assume xlimpnfvlem2.f: |- ( ph -> F : Z --> RR* )
  assume xlimpnfvlem2.g: |- ( ph -> A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) x < ( F ` k ) )

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
  assert |- ( ph -> F ~~>* +oo )

  proof
    wph
    cF
    cpnf
    clsxlim
    wbr
    #
    cF
    cpnf
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
    cpnf
    cxr
    wcel
    #
    cpnf
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
    #
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
    xlimpnfvlem2.f
    @22
    wph
    cM
    cZ
    xlimpnfvlem2.z
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
    pnfxr
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
    @25
    @7
    wa
    vx
    cv
    #
    cpnf
    cioc
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
    @24
    @7
    @29
    wph
    vx
    @6
    pnfnei
    adantll
    wph
    @29
    @17
    wi
    @24
    @7
    wph
    @28
    @17
    vx
    cr
    wph
    @26
    cr
    wcel
    #
    wa
    #
    @28
    wa
    #
    @16
    vj
    cZ
    wrex
    #
    @17
    @32
    @26
    @11
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
    @31
    @28
    vj
    wph
    @30
    vj
    xlimpnfvlem2.j
    @30
    vj
    nfv
    nfan
    @28
    vj
    nfv
    nfan
    @32
    @14
    cZ
    wcel
    #
    @35
    @16
    @32
    @36
    @35
    wa
    wa
    @35
    @16
    @32
    @36
    @35
    simprr
    @32
    @36
    @35
    @16
    wi
    @35
    @32
    @36
    wa
    #
    @34
    @13
    vk
    @15
    @32
    @36
    vk
    @31
    @28
    vk
    wph
    @30
    vk
    xlimpnfvlem2.k
    @30
    vk
    nfv
    nfan
    @28
    vk
    nfv
    nfan
    @36
    vk
    nfv
    nfan
    @37
    @8
    @15
    wcel
    #
    wa
    #
    @34
    @13
    @39
    @34
    wa
    #
    @10
    @12
    wph
    @30
    @28
    @36
    @38
    @34
    @10
    wph
    @36
    @38
    @10
    @28
    @34
    wph
    @36
    @38
    w3a
    #
    @8
    cZ
    @9
    @36
    @38
    @8
    cZ
    wcel
    #
    wph
    cM
    @8
    @14
    cZ
    xlimpnfvlem2.z
    uztrn2
    #
    3adant1
    #
    wph
    @36
    @9
    cZ
    wceq
    @38
    wph
    cZ
    cxr
    cF
    xlimpnfvlem2.f
    fdmd
    3ad2ant1
    eleqtrrd
    ad5ant134
    adantl4r
    @40
    @27
    @6
    @11
    wph
    @30
    @28
    @36
    @38
    @34
    @28
    wph
    @28
    @36
    @38
    @34
    simp-4r
    adantl4r
    @31
    @36
    @38
    @34
    @11
    @27
    wcel
    @28
    @31
    @36
    wa
    @38
    wa
    #
    @34
    wa
    #
    @26
    cpnf
    @11
    @46
    @30
    @26
    cxr
    wcel
    wph
    @30
    @36
    @38
    @34
    simp-4r
    @26
    rexr
    syl
    @5
    @46
    pnfxr
    a1i
    @46
    wph
    @42
    @11
    cxr
    wcel
    wph
    @30
    @36
    @38
    @34
    simp-4l
    @36
    @38
    @42
    @31
    @34
    @43
    ad4ant23
    wph
    cZ
    cxr
    @8
    cF
    xlimpnfvlem2.f
    ffvelrnda
    syl2anc
    @45
    @34
    simpr
    wph
    @36
    @38
    @11
    cpnf
    cle
    wbr
    @30
    @34
    @41
    @11
    @41
    cZ
    cxr
    @8
    cF
    wph
    @36
    @21
    @38
    xlimpnfvlem2.f
    3ad2ant1
    @44
    ffvelrnd
    pnfged
    ad5ant134
    eliocd
    ad5ant1345
    sseldd
    jca
    ex
    ralimda
    adantrr
    mpd
    3impb
    @31
    @35
    vj
    cZ
    wrex
    #
    @28
    wph
    @47
    vx
    cr
    xlimpnfvlem2.g
    r19.21bi
    adantr
    reximdd
    wph
    @33
    @17
    wb
    #
    @30
    @28
    wph
    cM
    cz
    wcel
    @48
    xlimpnfvlem2.m
    @13
    vj
    vk
    cM
    cZ
    xlimpnfvlem2.z
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
    cpnf
    vj
    vk
    cF
    @1
    cxr
    vk
    cF
    nfcv
    @23
    lmbr3
    mpbird
    @0
    @3
    wb
    wph
    cF
    cpnf
    clsxlim
    @2
    df-xlim
    breqi
    a1i
    mpbird
end
