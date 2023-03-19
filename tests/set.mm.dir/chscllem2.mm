include "ccau.mm"
include "wcel.mm"
include "cv.mm"
include "chli.mm"
include "wbr.mm"
include "chil.mm"
include "wrex.mm"
include "cdm.mm"
include "cn.mm"
include "wf.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "crp.mm"
include "chscllem1.mm"
include "cch.mm"
include "wss.mm"
include "chss.mm"
include "syl.mm"
include "fssd.mm"
include "wa.mm"
include "hlimcaui.mm"
include "hcaucvg.mm"
include "sylan.mm"
include "wi.mm"
include "eluznn.mm"
include "adantll.mm"
include "cle.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cc0.mm"
include "cr.mm"
include "cph.mm"
include "csh.mm"
include "chsh.mm"
include "shscl.mm"
include "syl2anc.mm"
include "shss.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "adantrr.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "hvsubcl.mm"
include "normcl.mm"
include "sqge0d.mm"
include "resqcld.mm"
include "addge01d.mm"
include "mpbid.mm"
include "cva.mm"
include "csp.mm"
include "wceq.mm"
include "cort.mm"
include "shsubcl.mm"
include "syl3anc.mm"
include "hvsubsub4.mm"
include "syl22anc.mm"
include "ocsh.mm"
include "cpjh.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wb.mm"
include "shless.mm"
include "syl31anc.mm"
include "shscom.mm"
include "3sstr4d.mm"
include "pjpreeq.mm"
include "simprd.mm"
include "sselda.mm"
include "hvsubadd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "risset.mm"
include "sylibr.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "adantrl.mm"
include "eqeltrd.mm"
include "shocorth.mm"
include "mp2and.mm"
include "normpyth.mm"
include "mpd.mm"
include "hvpncan3.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "normge0.mm"
include "le2sqd.mm"
include "adantlr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "mpand.mm"
include "anassrs.mm"
include "syldan.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ralrimiva.mm"
include "hcau.mm"
include "sylanbrc.mm"
include "ax-hcompl.mm"
include "wfn.mm"
include "hlimf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnbr.mm"
include "mpan.mm"
include "rexlimivw.mm"
include "3syl.mm"

theorem chscllem2
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cH: class H
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vk: setvar k
  let cG: class G
  let cN: class N
  assume chscl.1: |- ( ph -> A e. CH )
  assume chscl.2: |- ( ph -> B e. CH )
  assume chscl.3: |- ( ph -> B C_ ( _|_ ` A ) )
  assume chscl.4: |- ( ph -> H : NN --> ( A +H B ) )
  assume chscl.5: |- ( ph -> H ~~>v u )
  assume chscl.6: |- F = ( n e. NN |-> ( ( projh ` A ) ` ( H ` n ) ) )

  disjoint n u
  disjoint A n
  disjoint A u
  disjoint n ph
  disjoint B n
  disjoint B u
  disjoint H n
  disjoint H u
  disjoint f j
  disjoint f n
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C z
  disjoint j k
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint f k
  disjoint f ph
  disjoint j ph
  disjoint k n
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint H j
  disjoint k u
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint N n
  disjoint N z
  assert |- ( ph -> F e. dom ~~>v )

  proof
    wph
    cF
    ccau
    wcel
    #
    cF
    vx
    cv
    #
    chli
    wbr
    #
    vx
    chil
    wrex
    cF
    chli
    cdm
    #
    wcel
    #
    wph
    cn
    chil
    cF
    wf
    vj
    cv
    #
    cF
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    @1
    clt
    wbr
    #
    vk
    @5
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
    crp
    wral
    @0
    wph
    cn
    cA
    chil
    cF
    wph
    vu
    cA
    cB
    vn
    cF
    cH
    chscl.1
    chscl.2
    chscl.3
    chscl.4
    chscl.5
    chscl.6
    chscllem1
    #
    wph
    cA
    cch
    wcel
    #
    cA
    chil
    wss
    #
    chscl.1
    cA
    chss
    syl
    #
    fssd
    wph
    @14
    vx
    crp
    wph
    @1
    crp
    wcel
    #
    wa
    #
    @5
    cH
    cfv
    #
    @7
    cH
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    @1
    clt
    wbr
    #
    vk
    @12
    wral
    #
    vj
    cn
    wrex
    #
    @14
    wph
    cH
    ccau
    wcel
    #
    @19
    @27
    wph
    cH
    vu
    cv
    #
    chli
    wbr
    @28
    chscl.5
    @29
    cH
    hlimcaui
    syl
    vj
    vk
    @1
    cH
    hcaucvg
    sylan
    @20
    @26
    @13
    vj
    cn
    @20
    @5
    cn
    wcel
    #
    wa
    #
    @25
    @11
    vk
    @12
    @31
    @7
    @12
    wcel
    #
    @7
    cn
    wcel
    #
    @25
    @11
    wi
    #
    @30
    @32
    @33
    @20
    @7
    @5
    eluznn
    adantll
    @20
    @30
    @33
    @34
    @20
    @30
    @33
    wa
    #
    wa
    #
    @10
    @24
    cle
    wbr
    #
    @25
    @11
    wph
    @35
    @37
    @19
    wph
    @35
    wa
    #
    @37
    @10
    c2
    cexp
    co
    #
    @24
    c2
    cexp
    co
    #
    cle
    wbr
    @38
    @39
    @39
    @23
    @9
    cmv
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @40
    cle
    @38
    cc0
    @43
    cle
    wbr
    @39
    @44
    cle
    wbr
    @38
    @42
    @38
    @41
    chil
    wcel
    #
    @42
    cr
    wcel
    @38
    @23
    chil
    wcel
    #
    @9
    chil
    wcel
    #
    @45
    @38
    @21
    chil
    wcel
    #
    @22
    chil
    wcel
    #
    @46
    wph
    @30
    @48
    @33
    wph
    @30
    wa
    #
    cA
    cB
    cph
    co
    #
    chil
    @21
    wph
    @51
    chil
    wss
    #
    @30
    wph
    @51
    csh
    wcel
    #
    @52
    wph
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    @53
    wph
    @16
    @54
    chscl.1
    cA
    chsh
    syl
    #
    wph
    cB
    cch
    wcel
    @55
    chscl.2
    cB
    chsh
    syl
    #
    cA
    cB
    shscl
    syl2anc
    @51
    shss
    syl
    #
    adantr
    wph
    cn
    @51
    @5
    cH
    chscl.4
    ffvelrnda
    #
    sseldd
    #
    adantrr
    #
    @38
    cn
    chil
    @7
    cH
    wph
    cn
    chil
    cH
    wf
    @35
    wph
    cn
    @51
    chil
    cH
    chscl.4
    @58
    fssd
    adantr
    wph
    @30
    @33
    simprr
    #
    ffvelrnd
    #
    @21
    @22
    hvsubcl
    syl2anc
    #
    @38
    @6
    chil
    wcel
    #
    @8
    chil
    wcel
    #
    @47
    wph
    @30
    @65
    @33
    @50
    cA
    chil
    @6
    wph
    @17
    @30
    @18
    adantr
    wph
    cn
    cA
    @5
    cF
    @15
    ffvelrnda
    #
    sseldd
    #
    adantrr
    #
    @38
    cA
    chil
    @8
    wph
    @17
    @35
    @18
    adantr
    #
    @38
    cn
    cA
    @7
    cF
    wph
    cn
    cA
    cF
    wf
    @35
    @15
    adantr
    @62
    ffvelrnd
    #
    sseldd
    #
    @6
    @8
    hvsubcl
    syl2anc
    #
    @23
    @9
    hvsubcl
    syl2anc
    #
    @41
    normcl
    syl
    #
    sqge0d
    @38
    @39
    @43
    @38
    @10
    @38
    @47
    @10
    cr
    wcel
    #
    @73
    @9
    normcl
    syl
    #
    resqcld
    @38
    @42
    @75
    resqcld
    addge01d
    mpbid
    @38
    @9
    @41
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @44
    @40
    @38
    @9
    @41
    csp
    co
    cc0
    wceq
    #
    @80
    @44
    wceq
    #
    @38
    @9
    cA
    wcel
    #
    @41
    cA
    cort
    cfv
    #
    wcel
    #
    @81
    @38
    @54
    @6
    cA
    wcel
    #
    @8
    cA
    wcel
    @83
    wph
    @54
    @35
    @56
    adantr
    #
    wph
    @30
    @86
    @33
    @67
    adantrr
    @71
    @6
    @8
    cA
    shsubcl
    syl3anc
    @38
    @41
    @21
    @6
    cmv
    co
    #
    @22
    @8
    cmv
    co
    #
    cmv
    co
    #
    @84
    @38
    @48
    @49
    @65
    @66
    @41
    @90
    wceq
    @61
    @63
    @69
    @72
    @21
    @22
    @6
    @8
    hvsubsub4
    syl22anc
    @38
    @84
    csh
    wcel
    #
    @88
    @84
    wcel
    #
    @89
    @84
    wcel
    #
    @90
    @84
    wcel
    @38
    @17
    @91
    @70
    cA
    ocsh
    #
    syl
    wph
    @30
    @92
    @33
    @50
    @1
    @88
    wceq
    #
    vx
    @84
    wrex
    #
    @92
    @50
    @96
    @21
    @6
    @1
    cva
    co
    #
    wceq
    #
    vx
    @84
    wrex
    #
    @50
    @86
    @99
    @50
    @21
    cA
    cpjh
    cfv
    #
    cfv
    #
    @6
    wceq
    #
    @86
    @99
    wa
    #
    @30
    @102
    wph
    @30
    @6
    @101
    vn
    @5
    vn
    cv
    #
    cH
    cfv
    #
    @100
    cfv
    @101
    cn
    cF
    @104
    @5
    wceq
    @105
    @21
    @100
    @104
    @5
    cH
    fveq2
    fveq2d
    chscl.6
    @21
    @100
    fvex
    fvmpt
    eqcomd
    adantl
    @50
    @16
    @21
    cA
    @84
    cph
    co
    #
    wcel
    @102
    @103
    wb
    wph
    @16
    @30
    chscl.1
    adantr
    @50
    @51
    @106
    @21
    wph
    @51
    @106
    wss
    @30
    wph
    cB
    cA
    cph
    co
    #
    @84
    cA
    cph
    co
    #
    @51
    @106
    wph
    @55
    @91
    @54
    cB
    @84
    wss
    @107
    @108
    wss
    @57
    wph
    @17
    @91
    @18
    @94
    syl
    #
    @56
    chscl.3
    cB
    @84
    cA
    shless
    syl31anc
    wph
    @54
    @55
    @51
    @107
    wceq
    @56
    @57
    cA
    cB
    shscom
    syl2anc
    wph
    @54
    @91
    @106
    @108
    wceq
    @56
    @109
    cA
    @84
    shscom
    syl2anc
    3sstr4d
    adantr
    @59
    sseldd
    vx
    @21
    @6
    cA
    pjpreeq
    syl2anc
    mpbid
    simprd
    @50
    @95
    @98
    vx
    @84
    @50
    @1
    @84
    wcel
    #
    wa
    #
    @88
    @1
    wceq
    #
    @97
    @21
    wceq
    #
    @95
    @98
    @111
    @48
    @65
    @1
    chil
    wcel
    @112
    @113
    wb
    @50
    @48
    @110
    @60
    adantr
    @50
    @65
    @110
    @68
    adantr
    @50
    @84
    chil
    @1
    wph
    @84
    chil
    wss
    #
    @30
    wph
    @91
    @114
    @109
    @84
    shss
    syl
    adantr
    sselda
    @21
    @6
    @1
    hvsubadd
    syl3anc
    @1
    @88
    eqcom
    @21
    @97
    eqcom
    3bitr4g
    rexbidva
    mpbird
    vx
    @88
    @84
    risset
    sylibr
    #
    adantrr
    wph
    @33
    @93
    @30
    @50
    @92
    wi
    wph
    @33
    wa
    #
    @93
    wi
    vj
    vk
    @5
    @7
    wceq
    #
    @50
    @116
    @92
    @93
    @117
    @30
    @33
    wph
    @5
    @7
    cn
    eleq1
    anbi2d
    @117
    @88
    @89
    @84
    @117
    @21
    @22
    @6
    @8
    cmv
    @5
    @7
    cH
    fveq2
    @5
    @7
    cF
    fveq2
    oveq12d
    eleq1d
    imbi12d
    @115
    chvarv
    adantrl
    @88
    @89
    @84
    shsubcl
    syl3anc
    eqeltrd
    @38
    @54
    @83
    @85
    wa
    @81
    wi
    @87
    @9
    @41
    cA
    shocorth
    syl
    mp2and
    @38
    @47
    @45
    @81
    @82
    wi
    @73
    @74
    @9
    @41
    normpyth
    syl2anc
    mpd
    @38
    @79
    @24
    c2
    cexp
    @38
    @78
    @23
    cno
    @38
    @47
    @46
    @78
    @23
    wceq
    @73
    @64
    @9
    @23
    hvpncan3
    syl2anc
    fveq2d
    oveq1d
    eqtr3d
    breqtrd
    @38
    @10
    @24
    @77
    @38
    @46
    @24
    cr
    wcel
    #
    @64
    @23
    normcl
    syl
    #
    @38
    @47
    cc0
    @10
    cle
    wbr
    @73
    @9
    normge0
    syl
    @38
    @46
    cc0
    @24
    cle
    wbr
    @64
    @23
    normge0
    syl
    le2sqd
    mpbird
    adantlr
    @36
    @76
    @118
    @1
    cr
    wcel
    #
    @37
    @25
    wa
    @11
    wi
    wph
    @35
    @76
    @19
    @77
    adantlr
    wph
    @35
    @118
    @19
    @119
    adantlr
    @19
    @120
    wph
    @35
    @1
    rpre
    ad2antlr
    @10
    @24
    @1
    lelttr
    syl3anc
    mpand
    anassrs
    syldan
    ralimdva
    reximdva
    mpd
    ralrimiva
    vx
    vj
    vk
    cF
    hcau
    sylanbrc
    vx
    cF
    ax-hcompl
    @2
    @4
    vx
    chil
    chli
    @3
    wfn
    #
    @2
    @4
    @3
    chil
    chli
    wf
    @121
    hlimf
    @3
    chil
    chli
    ffn
    ax-mp
    @3
    cF
    @1
    chli
    fnbr
    mpan
    rexlimivw
    3syl
end
