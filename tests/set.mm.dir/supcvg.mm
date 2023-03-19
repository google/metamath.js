include "cn.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "ccom.mm"
include "cli.mm"
include "wrex.mm"
include "wcel.mm"
include "clt.mm"
include "cr.mm"
include "csup.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "crp.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "feq3.mm"
include "syl5ibcom.mm"
include "f00.mm"
include "simprbi.mm"
include "syl6.mm"
include "necon3d.mm"
include "mpd.mm"
include "3jca.mm"
include "suprcl.mm"
include "syl5eqel.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "ltsubrp.mm"
include "syl2an.mm"
include "eqbrtrd.mm"
include "syl6breq.mm"
include "wb.mm"
include "adantr.mm"
include "nnrecre.mm"
include "resubcl.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "suprlub.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wi.mm"
include "sselda.mm"
include "ltle.mm"
include "reximdva.mm"
include "crn.mm"
include "forn.mm"
include "rexeqdv.mm"
include "wfn.mm"
include "ffn.mm"
include "breq2.mm"
include "rexrn.mm"
include "3syl.mm"
include "bitr3d.mm"
include "ralrimiva.mm"
include "nnenom.mm"
include "fveq2.mm"
include "breq2d.mm"
include "axcc4.mm"
include "cvv.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cc.mm"
include "cz.mm"
include "recnd.mm"
include "1z.mm"
include "cuz.mm"
include "eqimss2i.mm"
include "nnex.mm"
include "climconst2.mm"
include "sylancl.mm"
include "mptex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ax-1cn.mm"
include "divcnv.mm"
include "mp1i.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "climsub.mm"
include "subid1d.mm"
include "breqtrd.mm"
include "ad2antrr.mm"
include "fex.mm"
include "vex.mm"
include "coexg.mm"
include "fssd.mm"
include "fco.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "simplr.mm"
include "fvco3.mm"
include "breqtrrd.mm"
include "ad3antrrr.mm"
include "syldan.mm"
include "suprub.mm"
include "syl6breqr.mm"
include "climsqz.mm"
include "ex.mm"
include "imdistanda.mm"
include "eximdv.mm"

theorem supcvg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cX: class X
  let vk: setvar k
  let vm: setvar m
  let vz: setvar z
  assume supcvg.1: |- X e. _V
  assume supcvg.2: |- S = sup ( A , RR , < )
  assume supcvg.3: |- R = ( n e. NN |-> ( S - ( 1 / n ) ) )
  assume supcvg.4: |- ( ph -> X =/= (/) )
  assume supcvg.5: |- ( ph -> F : X -onto-> A )
  assume supcvg.6: |- ( ph -> A C_ RR )
  assume supcvg.7: |- ( ph -> E. x e. RR A. y e. A y <_ x )

  disjoint f x
  disjoint F f
  disjoint F x
  disjoint f n
  disjoint f ph
  disjoint n ph
  disjoint R f
  disjoint R x
  disjoint X f
  disjoint X x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint S n
  disjoint f k
  disjoint f m
  disjoint f z
  disjoint k m
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint x z
  disjoint F z
  disjoint k n
  disjoint k ph
  disjoint m n
  disjoint m ph
  disjoint n z
  disjoint ph z
  disjoint R k
  disjoint R m
  disjoint R z
  disjoint X k
  disjoint X m
  disjoint X z
  disjoint y z
  disjoint A z
  disjoint S k
  disjoint S m
  assert |- ( ph -> E. f ( f : NN --> X /\ ( F o. f ) ~~> S ) )

  proof
    wph
    cn
    cX
    vf
    cv
    #
    wf
    #
    vk
    cv
    #
    cR
    cfv
    #
    @2
    @0
    cfv
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
    #
    wa
    #
    vf
    wex
    #
    @1
    cF
    @0
    ccom
    #
    cS
    cli
    wbr
    #
    wa
    #
    vf
    wex
    wph
    @3
    vx
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vx
    cX
    wrex
    #
    vk
    cn
    wral
    @9
    wph
    @16
    vk
    cn
    wph
    @2
    cn
    wcel
    #
    wa
    #
    @3
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    @16
    @18
    @3
    @19
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    @21
    @18
    @3
    cA
    cr
    clt
    csup
    #
    clt
    wbr
    #
    @23
    @18
    @3
    cS
    @24
    clt
    @18
    @3
    cS
    c1
    @2
    cdiv
    co
    #
    cmin
    co
    #
    cS
    clt
    @17
    @3
    @27
    wceq
    wph
    vn
    @2
    cS
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmin
    co
    #
    @27
    cn
    cR
    vn
    vk
    weq
    @29
    @26
    cS
    cmin
    @28
    @2
    c1
    cdiv
    oveq2
    #
    oveq2d
    supcvg.3
    cS
    @26
    cmin
    ovex
    fvmpt
    adantl
    #
    wph
    cS
    cr
    wcel
    #
    @26
    crp
    wcel
    @27
    cS
    clt
    wbr
    @17
    wph
    cS
    @24
    cr
    supcvg.2
    wph
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    @13
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    @24
    cr
    wcel
    wph
    @34
    @35
    @36
    supcvg.6
    wph
    cX
    c0
    wne
    @35
    supcvg.4
    wph
    cA
    c0
    cX
    c0
    wph
    cA
    c0
    wceq
    #
    cX
    c0
    cF
    wf
    #
    cX
    c0
    wceq
    #
    wph
    cX
    cA
    cF
    wf
    #
    @38
    @39
    wph
    cX
    cA
    cF
    wfo
    #
    @41
    supcvg.5
    cX
    cA
    cF
    fof
    syl
    #
    cA
    c0
    cX
    cF
    feq3
    syl5ibcom
    @39
    cF
    c0
    wceq
    @40
    cX
    cF
    f00
    simprbi
    syl6
    necon3d
    mpd
    supcvg.7
    3jca
    #
    vx
    vy
    cA
    suprcl
    syl
    syl5eqel
    #
    @17
    @2
    @2
    nnrp
    rpreccld
    cS
    @26
    ltsubrp
    syl2an
    eqbrtrd
    supcvg.2
    syl6breq
    @18
    @37
    @3
    cr
    wcel
    #
    @25
    @23
    wb
    wph
    @37
    @17
    @44
    adantr
    wph
    cn
    cr
    @2
    cR
    wph
    vn
    cn
    @30
    cr
    cR
    wph
    @33
    @29
    cr
    wcel
    @30
    cr
    wcel
    @28
    cn
    wcel
    @45
    @28
    nnrecre
    cS
    @29
    resubcl
    syl2an
    supcvg.3
    fmptd
    #
    ffvelrnda
    #
    vx
    vy
    vz
    cA
    @3
    suprlub
    syl2anc
    mpbid
    @18
    @22
    @20
    vz
    cA
    @18
    @19
    cA
    wcel
    #
    wa
    @46
    @19
    cr
    wcel
    @22
    @20
    wi
    @18
    @46
    @49
    @48
    adantr
    @18
    cA
    cr
    @19
    wph
    @34
    @17
    supcvg.6
    adantr
    sselda
    @3
    @19
    ltle
    syl2anc
    reximdva
    mpd
    wph
    @21
    @16
    wb
    @17
    wph
    @20
    vz
    cF
    crn
    #
    wrex
    #
    @21
    @16
    wph
    @20
    vz
    @50
    cA
    wph
    @42
    @50
    cA
    wceq
    supcvg.5
    cX
    cA
    cF
    forn
    syl
    rexeqdv
    wph
    @41
    cF
    cX
    wfn
    @51
    @16
    wb
    @43
    cX
    cA
    cF
    ffn
    @20
    @15
    vz
    vx
    cX
    cF
    @19
    @14
    @3
    cle
    breq2
    rexrn
    3syl
    bitr3d
    adantr
    mpbid
    ralrimiva
    @15
    @6
    vx
    cX
    vf
    vk
    cn
    supcvg.1
    nnenom
    @13
    @4
    wceq
    @14
    @5
    @3
    cle
    @13
    @4
    cF
    fveq2
    breq2d
    axcc4
    syl
    wph
    @8
    @12
    vf
    wph
    @1
    @7
    @11
    wph
    @1
    wa
    #
    @7
    @11
    @52
    @7
    wa
    #
    cS
    vm
    cR
    @10
    c1
    cvv
    cn
    nnuz
    @53
    1zzd
    wph
    cR
    cS
    cli
    wbr
    @1
    @7
    wph
    cR
    cS
    cc0
    cmin
    co
    cS
    cli
    wph
    cS
    cc0
    vk
    cn
    cS
    csn
    cxp
    #
    vn
    cn
    @29
    cmpt
    #
    cR
    c1
    cvv
    cn
    nnuz
    wph
    1zzd
    wph
    cS
    cc
    wcel
    #
    c1
    cz
    wcel
    @54
    cS
    cli
    wbr
    wph
    cS
    @45
    recnd
    #
    1z
    cS
    c1
    cn
    cn
    c1
    cuz
    cfv
    nnuz
    eqimss2i
    nnex
    climconst2
    sylancl
    cR
    cvv
    wcel
    wph
    cR
    vn
    cn
    @30
    cmpt
    cvv
    supcvg.3
    vn
    cn
    @30
    nnex
    mptex
    eqeltri
    a1i
    c1
    cc
    wcel
    @55
    cc0
    cli
    wbr
    wph
    ax-1cn
    c1
    vn
    divcnv
    mp1i
    @18
    @2
    @54
    cfv
    #
    cS
    cc
    wph
    @33
    @17
    @58
    cS
    wceq
    @45
    cn
    cS
    @2
    cr
    fvconst2g
    sylan
    #
    wph
    @56
    @17
    @57
    adantr
    eqeltrd
    @18
    @2
    @55
    cfv
    #
    @26
    cc
    @17
    @60
    @26
    wceq
    wph
    vn
    @2
    @29
    @26
    cn
    @55
    @31
    @55
    eqid
    c1
    @2
    cdiv
    ovex
    fvmpt
    adantl
    #
    @17
    @26
    cc
    wcel
    wph
    @17
    @26
    @2
    nnrecre
    recnd
    adantl
    eqeltrd
    @18
    @3
    @27
    @58
    @60
    cmin
    co
    @32
    @18
    @58
    cS
    @60
    @26
    cmin
    @59
    @61
    oveq12d
    eqtr4d
    climsub
    wph
    cS
    @57
    subid1d
    breqtrd
    ad2antrr
    @53
    cF
    cvv
    wcel
    #
    @0
    cvv
    wcel
    @10
    cvv
    wcel
    @53
    @41
    cX
    cvv
    wcel
    @62
    wph
    @41
    @1
    @7
    @43
    ad2antrr
    #
    supcvg.1
    cX
    cA
    cvv
    cF
    fex
    sylancl
    vf
    vex
    cF
    @0
    cvv
    cvv
    coexg
    sylancl
    @53
    cn
    cr
    vm
    cv
    #
    cR
    wph
    cn
    cr
    cR
    wf
    @1
    @7
    @47
    ad2antrr
    ffvelrnda
    @53
    cn
    cr
    @64
    @10
    @52
    cn
    cr
    @10
    wf
    #
    @7
    wph
    cX
    cr
    cF
    wf
    @1
    @65
    wph
    cX
    cA
    cr
    cF
    @43
    supcvg.6
    fssd
    cn
    cX
    cr
    cF
    @0
    fco
    sylan
    adantr
    ffvelrnda
    @53
    @64
    cn
    wcel
    #
    wa
    #
    @64
    cR
    cfv
    #
    @64
    @0
    cfv
    #
    cF
    cfv
    #
    @64
    @10
    cfv
    #
    cle
    @7
    @66
    @68
    @70
    cle
    wbr
    #
    @52
    @6
    @72
    vk
    @64
    cn
    vk
    vm
    weq
    #
    @3
    @68
    @5
    @70
    cle
    @2
    @64
    cR
    fveq2
    @73
    @4
    @69
    cF
    @2
    @64
    @0
    fveq2
    fveq2d
    breq12d
    rspccva
    adantll
    @53
    @1
    @66
    @71
    @70
    wceq
    wph
    @1
    @7
    simplr
    #
    cn
    cX
    @64
    cF
    @0
    fvco3
    sylan
    #
    breqtrrd
    @67
    @71
    @70
    cS
    cle
    @75
    @67
    @70
    @24
    cS
    cle
    @67
    @37
    @70
    cA
    wcel
    #
    @70
    @24
    cle
    wbr
    wph
    @37
    @1
    @7
    @66
    @44
    ad3antrrr
    @53
    @66
    @69
    cX
    wcel
    @76
    @53
    cn
    cX
    @64
    @0
    @74
    ffvelrnda
    @53
    cX
    cA
    @69
    cF
    @63
    ffvelrnda
    syldan
    vx
    vy
    cA
    @70
    suprub
    syl2anc
    supcvg.2
    syl6breqr
    eqbrtrd
    climsqz
    ex
    imdistanda
    eximdv
    mpd
end
