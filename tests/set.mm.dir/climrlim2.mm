include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "crli.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cle.mm"
include "wi.mm"
include "cr.mm"
include "cfl.mm"
include "cz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "sselda.mm"
include "flcld.mm"
include "adantlr.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "wb.mm"
include "flge.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simpr.mm"
include "ralimi.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "syl2im.mm"
include "adantr.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "sylc.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylibd.mm"
include "expr.mm"
include "com23.mm"
include "ralrimdva.mm"
include "eluzelre.mm"
include "adantl.mm"
include "jctild.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "ralimdva.mm"
include "adantld.mm"
include "cvv.mm"
include "climrel.mm"
include "brrelexi.mm"
include "syl.mm"
include "eqidd.mm"
include "clim2.mm"
include "climcl.mm"
include "rlim2.mm"
include "3imtr4d.mm"
include "mpd.mm"

theorem climrlim2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vn: setvar n
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vy: setvar y
  let vk: setvar k
  assume climrlim2.1: |- Z = ( ZZ>= ` M )
  assume climrlim2.2: |- ( n = ( |_ ` x ) -> B = C )
  assume climrlim2.3: |- ( ph -> A C_ RR )
  assume climrlim2.4: |- ( ph -> M e. ZZ )
  assume climrlim2.5: |- ( ph -> ( n e. Z |-> B ) ~~> D )
  assume climrlim2.6: |- ( ( ph /\ n e. Z ) -> B e. CC )
  assume climrlim2.7: |- ( ( ph /\ x e. A ) -> M <_ x )

  disjoint A x
  disjoint B x
  disjoint C n
  disjoint D x
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint Z n
  disjoint Z x
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint x y
  disjoint A y
  disjoint j k
  disjoint B j
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B y
  disjoint j n
  disjoint C j
  disjoint n y
  disjoint C y
  disjoint D j
  disjoint D k
  disjoint D y
  disjoint M j
  disjoint M k
  disjoint j ph
  disjoint k n
  disjoint k ph
  disjoint ph y
  disjoint Z j
  disjoint Z k
  disjoint Z y
  assert |- ( ph -> ( x e. A |-> C ) ~~>r D )

  proof
    wph
    vn
    cZ
    cB
    cmpt
    #
    cD
    cli
    wbr
    #
    vx
    cA
    cC
    cmpt
    cD
    crli
    wbr
    #
    climrlim2.5
    wph
    cD
    cc
    wcel
    #
    vk
    cv
    #
    @0
    cfv
    #
    cc
    wcel
    #
    @5
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
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
    cZ
    wrex
    #
    vy
    crp
    wral
    #
    wa
    @12
    vx
    cv
    #
    cle
    wbr
    #
    cC
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vj
    cr
    wrex
    #
    vy
    crp
    wral
    #
    @1
    @2
    wph
    @16
    @25
    @3
    wph
    @15
    @24
    vy
    crp
    wph
    @9
    crp
    wcel
    #
    wa
    #
    @14
    @23
    vj
    cZ
    cr
    @27
    @12
    cZ
    wcel
    #
    @14
    @12
    cr
    wcel
    #
    @23
    wa
    @27
    @28
    wa
    #
    @14
    @23
    @29
    @30
    @14
    @22
    vx
    cA
    @30
    @17
    cA
    wcel
    #
    wa
    @18
    @14
    @21
    @30
    @31
    @18
    @14
    @21
    wi
    @30
    @31
    @18
    wa
    #
    wa
    #
    @14
    @17
    cfl
    cfv
    #
    @0
    cfv
    #
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    @21
    @33
    @34
    @13
    wcel
    #
    @14
    @10
    vk
    @13
    wral
    @38
    @33
    @12
    cz
    wcel
    #
    @34
    cz
    wcel
    #
    @12
    @34
    cle
    wbr
    #
    @39
    @28
    @40
    @27
    @32
    @40
    @12
    cM
    cuz
    cfv
    #
    cZ
    cM
    @12
    eluzelz
    climrlim2.1
    eleq2s
    ad2antlr
    #
    @27
    @31
    @41
    @28
    @18
    wph
    @31
    @41
    @26
    wph
    @31
    wa
    #
    @17
    wph
    cA
    cr
    @17
    climrlim2.3
    sselda
    #
    flcld
    #
    adantlr
    ad2ant2r
    @33
    @18
    @42
    @30
    @31
    @18
    simprr
    @33
    @17
    cr
    wcel
    #
    @40
    @18
    @42
    wb
    @27
    @31
    @48
    @28
    @18
    wph
    @31
    @48
    @26
    @46
    adantlr
    ad2ant2r
    @44
    @17
    @12
    flge
    syl2anc
    mpbid
    @12
    @34
    eluz2
    syl3anbrc
    @11
    @10
    vk
    @13
    @6
    @10
    simpr
    ralimi
    @10
    @38
    vk
    @34
    @13
    @4
    @34
    wceq
    #
    @8
    @37
    @9
    clt
    @49
    @7
    @36
    cabs
    @49
    @5
    @35
    cD
    cmin
    @4
    @34
    @0
    fveq2
    oveq1d
    fveq2d
    breq1d
    rspcv
    syl2im
    @33
    @37
    @20
    @9
    clt
    @33
    @36
    @19
    cabs
    @33
    @35
    cC
    cD
    cmin
    @27
    @31
    @35
    cC
    wceq
    #
    @28
    @18
    wph
    @31
    @50
    @26
    @45
    @34
    cZ
    wcel
    #
    cC
    cc
    wcel
    #
    @50
    @45
    @34
    @43
    cZ
    @45
    cM
    cz
    wcel
    #
    @41
    cM
    @34
    cle
    wbr
    #
    @34
    @43
    wcel
    wph
    @53
    @31
    climrlim2.4
    adantr
    #
    @47
    @45
    cM
    @17
    cle
    wbr
    #
    @54
    climrlim2.7
    @45
    @48
    @53
    @56
    @54
    wb
    @46
    @55
    @17
    cM
    flge
    syl2anc
    mpbid
    cM
    @34
    eluz2
    syl3anbrc
    climrlim2.1
    syl6eleqr
    #
    @45
    @51
    cB
    cc
    wcel
    #
    vn
    cZ
    wral
    #
    @52
    @57
    wph
    @59
    @31
    wph
    @58
    vn
    cZ
    climrlim2.6
    ralrimiva
    adantr
    @58
    @52
    vn
    @34
    cZ
    vn
    cv
    @34
    wceq
    cB
    cC
    cc
    climrlim2.2
    eleq1d
    rspcv
    sylc
    #
    vn
    @34
    cB
    cC
    cZ
    cc
    @0
    climrlim2.2
    @0
    eqid
    fvmptg
    syl2anc
    adantlr
    ad2ant2r
    oveq1d
    fveq2d
    breq1d
    sylibd
    expr
    com23
    ralrimdva
    @28
    @29
    @27
    @29
    @12
    @43
    cZ
    cM
    @12
    eluzelre
    climrlim2.1
    eleq2s
    adantl
    jctild
    expimpd
    reximdv2
    ralimdva
    adantld
    wph
    vy
    cD
    @5
    vj
    vk
    @0
    cM
    cvv
    cZ
    climrlim2.1
    climrlim2.4
    wph
    @1
    @0
    cvv
    wcel
    climrlim2.5
    @0
    cD
    cli
    climrel
    brrelexi
    syl
    wph
    @4
    cZ
    wcel
    wa
    @5
    eqidd
    clim2
    wph
    vy
    vj
    vx
    cA
    cC
    cD
    wph
    @52
    vx
    cA
    @60
    ralrimiva
    climrlim2.3
    wph
    @1
    @3
    climrlim2.5
    cD
    @0
    climcl
    syl
    rlim2
    3imtr4d
    mpd
end
