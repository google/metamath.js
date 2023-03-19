include "cpnf.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cr.mm"
include "cres.mm"
include "wf.mm"
include "wrex.mm"
include "wa.mm"
include "cmnf.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cz.mm"
include "ad2antrr.mm"
include "cxr.mm"
include "cli.mm"
include "crp.mm"
include "simpr.mm"
include "recnd.mm"
include "adantr.mm"
include "subcld.mm"
include "wne.mm"
include "renepnf.mm"
include "necomd.mm"
include "syl.mm"
include "subne0d.mm"
include "absrpcld.mm"
include "renemnf.mm"
include "adantlr.mm"
include "ifcld.mm"
include "rpred.mm"
include "min1d.mm"
include "min2d.mm"
include "climxrrelem.mm"
include "wn.mm"
include "leidd.mm"
include "pm2.21.mm"
include "imp.mm"
include "adantll.mm"
include "pm2.61dan.mm"
include "ad4ant24.mm"
include "ad4ant13.mm"
include "wral.mm"
include "cdm.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simp-4l.mm"
include "uztrn2.mm"
include "wceq.mm"
include "fdmd.mm"
include "eleqtrrd.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "rspa.mm"
include "simpllr.mm"
include "nelne2.mm"
include "simp-4r.mm"
include "xrred.mm"
include "jca.mm"
include "ralrimia.mm"
include "wb.mm"
include "wfun.mm"
include "ffund.mm"
include "ffvresb.mm"
include "ad3antrrr.mm"
include "mpbird.mm"
include "c1.mm"
include "clt.mm"
include "r19.26.mm"
include "simplbi.mm"
include "ad2antll.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "cvv.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "eqidd.mm"
include "clim.mm"
include "mpbid.mm"
include "simprd.mm"
include "1rp.mm"
include "rspcdva.mm"
include "reximddv.mm"
include "rexuz3.mm"

theorem climxrre
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climxrre.m: |- ( ph -> M e. ZZ )
  assume climxrre.z: |- Z = ( ZZ>= ` M )
  assume climxrre.f: |- ( ph -> F : Z --> RR* )
  assume climxrre.a: |- ( ph -> A e. RR )
  assume climxrre.c: |- ( ph -> F ~~> A )

  disjoint A j
  disjoint F j
  disjoint M j
  disjoint Z j
  disjoint j ph
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint Z k
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> E. j e. Z ( F |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> RR )

  proof
    wph
    cpnf
    cc
    wcel
    #
    vj
    cv
    #
    cuz
    cfv
    #
    cr
    cF
    @2
    cres
    wf
    #
    vj
    cZ
    wrex
    #
    wph
    @0
    wa
    #
    cmnf
    cc
    wcel
    #
    @4
    @5
    @6
    wa
    #
    cA
    cpnf
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cmnf
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    @9
    @11
    cif
    #
    vj
    cF
    cM
    cZ
    wph
    cM
    cz
    wcel
    #
    @0
    @6
    climxrre.m
    ad2antrr
    climxrre.z
    wph
    cZ
    cxr
    cF
    wf
    #
    @0
    @6
    climxrre.f
    ad2antrr
    wph
    cF
    cA
    cli
    wbr
    #
    @0
    @6
    climxrre.c
    ad2antrr
    @7
    @12
    @9
    @11
    crp
    @5
    @9
    crp
    wcel
    #
    @6
    @5
    @8
    @5
    cpnf
    cA
    wph
    @0
    simpr
    #
    wph
    cA
    cc
    wcel
    #
    @0
    wph
    cA
    climxrre.a
    recnd
    #
    adantr
    #
    subcld
    @5
    cpnf
    cA
    @18
    @21
    wph
    cpnf
    cA
    wne
    #
    @0
    wph
    cA
    cr
    wcel
    #
    @22
    climxrre.a
    @23
    cA
    cpnf
    cA
    renepnf
    necomd
    syl
    adantr
    subne0d
    absrpcld
    #
    adantr
    #
    wph
    @6
    @11
    crp
    wcel
    #
    @0
    wph
    @6
    wa
    #
    @10
    @27
    cmnf
    cA
    wph
    @6
    simpr
    #
    wph
    @19
    @6
    @20
    adantr
    #
    subcld
    @27
    cmnf
    cA
    @28
    @29
    @27
    @23
    cmnf
    cA
    wne
    wph
    @23
    @6
    climxrre.a
    adantr
    @23
    cA
    cmnf
    cA
    renemnf
    necomd
    syl
    subne0d
    absrpcld
    #
    adantlr
    #
    ifcld
    @7
    @13
    @9
    cle
    wbr
    @0
    @7
    @9
    @11
    @7
    @9
    @25
    rpred
    #
    @7
    @11
    @31
    rpred
    #
    min1d
    adantr
    @7
    @13
    @11
    cle
    wbr
    @6
    @7
    @9
    @11
    @32
    @33
    min2d
    adantr
    climxrrelem
    @5
    @6
    wn
    #
    wa
    cA
    @9
    vj
    cF
    cM
    cZ
    wph
    @14
    @0
    @34
    climxrre.m
    ad2antrr
    climxrre.z
    wph
    @15
    @0
    @34
    climxrre.f
    ad2antrr
    wph
    @16
    @0
    @34
    climxrre.c
    ad2antrr
    @5
    @17
    @34
    @24
    adantr
    @5
    @9
    @9
    cle
    wbr
    @34
    @0
    @5
    @9
    @5
    @9
    @24
    rpred
    leidd
    ad2antrr
    @34
    @6
    @12
    @5
    @34
    @6
    @12
    @6
    @12
    pm2.21
    imp
    adantll
    climxrrelem
    pm2.61dan
    wph
    @0
    wn
    #
    wa
    #
    @6
    @4
    @36
    @6
    wa
    cA
    @11
    vj
    cF
    cM
    cZ
    wph
    @14
    @35
    @6
    climxrre.m
    ad2antrr
    climxrre.z
    wph
    @15
    @35
    @6
    climxrre.f
    ad2antrr
    wph
    @16
    @35
    @6
    climxrre.c
    ad2antrr
    wph
    @6
    @26
    @35
    @30
    adantlr
    @35
    @0
    @11
    @9
    cle
    wbr
    #
    wph
    @6
    @35
    @0
    @37
    @0
    @37
    pm2.21
    imp
    ad4ant24
    wph
    @6
    @11
    @11
    cle
    wbr
    @35
    @6
    @27
    @11
    @27
    @11
    @30
    rpred
    leidd
    ad4ant13
    climxrrelem
    @36
    @34
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    vk
    @2
    wral
    #
    @3
    vj
    cZ
    @38
    @1
    cZ
    wcel
    #
    @42
    wa
    #
    wa
    #
    @3
    @39
    cF
    cdm
    #
    wcel
    #
    @40
    cr
    wcel
    #
    wa
    #
    vk
    @2
    wral
    #
    @45
    @49
    vk
    @2
    @38
    @44
    vk
    @38
    vk
    nfv
    @43
    @42
    vk
    @43
    vk
    nfv
    @41
    vk
    @2
    nfra1
    nfan
    nfan
    @45
    @39
    @2
    wcel
    #
    wa
    #
    @47
    @48
    @52
    wph
    @39
    cZ
    wcel
    #
    @47
    wph
    @35
    @34
    @44
    @51
    simp-4l
    #
    @44
    @51
    @53
    @38
    @43
    @51
    @53
    @42
    cM
    @39
    @1
    cZ
    climxrre.z
    uztrn2
    adantlr
    adantll
    #
    wph
    @53
    wa
    @39
    cZ
    @46
    wph
    @53
    simpr
    wph
    @46
    cZ
    wceq
    @53
    wph
    cZ
    cxr
    cF
    climxrre.f
    fdmd
    adantr
    eleqtrrd
    syl2anc
    @52
    @40
    @52
    wph
    @53
    @40
    cxr
    wcel
    @54
    @55
    wph
    cZ
    cxr
    @39
    cF
    climxrre.f
    ffvelrnda
    syl2anc
    @52
    @41
    @34
    @40
    cmnf
    wne
    @44
    @51
    @41
    @38
    @42
    @51
    @41
    @43
    @41
    vk
    @2
    rspa
    adantll
    adantll
    #
    @36
    @34
    @44
    @51
    simpllr
    @40
    cmnf
    cc
    nelne2
    syl2anc
    @52
    @41
    @35
    @40
    cpnf
    wne
    @56
    wph
    @35
    @34
    @44
    @51
    simp-4r
    @40
    cpnf
    cc
    nelne2
    syl2anc
    xrred
    jca
    ralrimia
    wph
    @3
    @50
    wb
    #
    @35
    @34
    @44
    wph
    cF
    wfun
    @57
    wph
    cZ
    cxr
    cF
    climxrre.f
    ffund
    vk
    @2
    cr
    cF
    ffvresb
    syl
    ad3antrrr
    mpbird
    wph
    @42
    vj
    cZ
    wrex
    #
    @35
    @34
    wph
    @58
    @42
    vj
    cz
    wrex
    #
    wph
    @41
    @40
    cA
    cmin
    co
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    vk
    @2
    wral
    #
    @42
    vj
    cz
    @63
    @42
    wph
    @1
    cz
    wcel
    @63
    @42
    @61
    vk
    @2
    wral
    @41
    @61
    vk
    @2
    r19.26
    simplbi
    ad2antll
    wph
    @41
    @60
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @2
    wral
    vj
    cz
    wrex
    #
    @63
    vj
    cz
    wrex
    vx
    crp
    c1
    @64
    c1
    wceq
    #
    @66
    @62
    vj
    vk
    cz
    @2
    @68
    @65
    @61
    @41
    @64
    c1
    @60
    clt
    breq2
    anbi2d
    rexralbidv
    wph
    @19
    @67
    vx
    crp
    wral
    #
    wph
    @16
    @19
    @69
    wa
    climxrre.c
    wph
    vx
    cA
    @40
    vj
    vk
    cF
    cvv
    wph
    cZ
    cxr
    cvv
    cF
    climxrre.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    climxrre.z
    fvexi
    a1i
    fexd
    wph
    @39
    cz
    wcel
    wa
    @40
    eqidd
    clim
    mpbid
    simprd
    c1
    crp
    wcel
    wph
    1rp
    a1i
    rspcdva
    reximddv
    wph
    @14
    @58
    @59
    wb
    climxrre.m
    @41
    vj
    vk
    cM
    cZ
    climxrre.z
    rexuz3
    syl
    mpbird
    ad2antrr
    reximddv
    pm2.61dan
    pm2.61dan
end
