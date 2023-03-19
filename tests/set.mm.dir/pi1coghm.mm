include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cghm.mm"
include "ctopon.mm"
include "pi1grp.mm"
include "syl2anc.mm"
include "cuni.mm"
include "ctop.mm"
include "ccn.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "jca.mm"
include "pi1cof.mm"
include "cphtpc.mm"
include "cqs.mm"
include "a1i.mm"
include "pi1bas2.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "cec.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cpco.mm"
include "ccom.mm"
include "cii.mm"
include "cc0.mm"
include "c1.mm"
include "w3a.mm"
include "pi1eluni.mm"
include "simp1d.mm"
include "adantr.mm"
include "simp3d.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "ad2antrr.mm"
include "copco.mm"
include "eceq1d.mm"
include "pcocn.mm"
include "pco0.mm"
include "eqtrd.mm"
include "pco1.mm"
include "mpbir3and.mm"
include "pi1coval.mm"
include "adantlr.mm"
include "syldan.mm"
include "cnco.mm"
include "cicc.mm"
include "iitopon.mm"
include "0elunit.mm"
include "fvco3.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "1elunit.mm"
include "eqidd.mm"
include "wb.mm"
include "pi1addval.mm"
include "3eqtr4d.mm"
include "simplr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "ectocld.mm"
include "ralrimiva.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "isghm.mm"
include "sylanbrc.mm"

theorem pi1coghm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vh: setvar h
  let vf: setvar f
  let vz: setvar z
  let vy: setvar y
  let cT: class T
  assume pi1co.p: |- P = ( J pi1 A )
  assume pi1co.q: |- Q = ( K pi1 B )
  assume pi1co.v: |- V = ( Base ` P )
  assume pi1co.g: |- G = ran ( g e. U. V |-> <. [ g ] ( ~=ph ` J ) , [ ( F o. g ) ] ( ~=ph ` K ) >. )
  assume pi1co.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1co.f: |- ( ph -> F e. ( J Cn K ) )
  assume pi1co.a: |- ( ph -> A e. X )
  assume pi1co.b: |- ( ph -> ( F ` A ) = B )

  disjoint A g
  disjoint F g
  disjoint J g
  disjoint g ph
  disjoint K g
  disjoint P g
  disjoint Q g
  disjoint V g
  disjoint g s
  disjoint A s
  disjoint g h
  disjoint h s
  disjoint F h
  disjoint F s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f z
  disjoint J f
  disjoint g z
  disjoint h z
  disjoint J h
  disjoint s z
  disjoint J s
  disjoint J z
  disjoint f y
  disjoint f ph
  disjoint g y
  disjoint h y
  disjoint h ph
  disjoint s y
  disjoint ph s
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint G f
  disjoint G h
  disjoint G y
  disjoint G z
  disjoint K h
  disjoint K s
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint T g
  disjoint T s
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint V f
  disjoint V h
  disjoint V s
  disjoint V y
  disjoint V z
  assert |- ( ph -> G e. ( P GrpHom Q ) )

  proof
    wph
    cP
    cgrp
    wcel
    #
    cQ
    cgrp
    wcel
    #
    wa
    cV
    cQ
    cbs
    cfv
    #
    cG
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    cP
    cplusg
    cfv
    #
    co
    #
    cG
    cfv
    #
    @4
    cG
    cfv
    #
    @5
    cG
    cfv
    #
    cQ
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cV
    wral
    #
    vy
    cV
    wral
    #
    wa
    cG
    cP
    cQ
    cghm
    co
    wcel
    wph
    @0
    @1
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    @0
    pi1co.j
    pi1co.a
    cP
    cJ
    cX
    cA
    pi1co.p
    pi1grp
    syl2anc
    wph
    cK
    cK
    cuni
    #
    ctopon
    cfv
    wcel
    #
    cB
    @18
    wcel
    #
    @1
    wph
    cK
    ctop
    wcel
    #
    @19
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @21
    pi1co.f
    cF
    cJ
    cK
    cntop2
    syl
    cK
    @18
    @18
    eqid
    toptopon
    sylib
    #
    wph
    cA
    cF
    cfv
    #
    cB
    @18
    pi1co.b
    wph
    cX
    @18
    cA
    cF
    wph
    @16
    @19
    @22
    cX
    @18
    cF
    wf
    pi1co.j
    @23
    pi1co.f
    cF
    cJ
    cK
    cX
    @18
    cnf2
    syl3anc
    pi1co.a
    ffvelrnd
    eqeltrrd
    #
    cQ
    cK
    @18
    cB
    pi1co.q
    pi1grp
    syl2anc
    jca
    wph
    @3
    @15
    wph
    cA
    cB
    cP
    cQ
    vg
    cF
    cG
    cJ
    cK
    cV
    cX
    pi1co.p
    pi1co.q
    pi1co.v
    pi1co.g
    pi1co.j
    pi1co.f
    pi1co.a
    pi1co.b
    pi1cof
    wph
    @14
    vy
    cV
    wph
    @4
    cV
    wcel
    #
    @4
    cV
    cuni
    #
    cJ
    cphtpc
    cfv
    #
    cqs
    #
    wcel
    #
    @14
    wph
    @26
    @30
    wph
    cV
    @29
    @4
    wph
    cV
    cP
    cJ
    cX
    cA
    pi1co.p
    pi1co.j
    pi1co.a
    cV
    cP
    cbs
    cfv
    wceq
    #
    wph
    pi1co.v
    a1i
    #
    pi1bas2
    #
    eleq2d
    biimpa
    vf
    cv
    #
    @28
    cec
    #
    @5
    @6
    co
    #
    cG
    cfv
    #
    @35
    cG
    cfv
    #
    @10
    @11
    co
    #
    wceq
    #
    vz
    cV
    wral
    #
    @14
    wph
    vf
    @4
    @27
    @28
    @29
    @29
    eqid
    #
    @35
    @4
    wceq
    #
    @40
    @13
    vz
    cV
    @43
    @37
    @8
    @39
    @12
    @43
    @36
    @7
    cG
    @35
    @4
    @5
    @6
    oveq1
    fveq2d
    @43
    @38
    @9
    @10
    @11
    @35
    @4
    cG
    fveq2
    oveq1d
    eqeq12d
    ralbidv
    wph
    @34
    @27
    wcel
    #
    wa
    #
    @41
    @40
    vz
    @29
    wral
    @45
    @40
    vz
    @29
    @35
    vh
    cv
    #
    @28
    cec
    #
    @6
    co
    #
    cG
    cfv
    #
    @38
    @47
    cG
    cfv
    #
    @11
    co
    #
    wceq
    @40
    @45
    vh
    @5
    @27
    @28
    @29
    @42
    @47
    @5
    wceq
    #
    @49
    @37
    @51
    @39
    @52
    @48
    @36
    cG
    @47
    @5
    @35
    @6
    oveq2
    fveq2d
    @52
    @50
    @10
    @38
    @11
    @47
    @5
    cG
    fveq2
    oveq2d
    eqeq12d
    @45
    @46
    @27
    wcel
    #
    wa
    #
    @34
    @46
    cJ
    cpco
    cfv
    co
    #
    @28
    cec
    #
    cG
    cfv
    #
    cF
    @34
    ccom
    #
    cK
    cphtpc
    cfv
    #
    cec
    #
    cF
    @46
    ccom
    #
    @59
    cec
    #
    @11
    co
    #
    @49
    @51
    @54
    cF
    @55
    ccom
    #
    @59
    cec
    #
    @58
    @61
    cK
    cpco
    cfv
    co
    #
    @59
    cec
    @57
    @63
    @54
    @64
    @66
    @59
    @54
    @34
    @46
    cF
    cJ
    cK
    @45
    @34
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @53
    @45
    @68
    cc0
    @34
    cfv
    #
    cA
    wceq
    #
    c1
    @34
    cfv
    #
    cA
    wceq
    #
    wph
    @44
    @68
    @70
    @72
    w3a
    wph
    cV
    @34
    cP
    cJ
    cX
    cA
    pi1co.p
    pi1co.j
    pi1co.a
    @32
    pi1eluni
    biimpa
    #
    simp1d
    #
    adantr
    #
    @54
    @46
    @67
    wcel
    #
    cc0
    @46
    cfv
    #
    cA
    wceq
    #
    c1
    @46
    cfv
    #
    cA
    wceq
    #
    @45
    @53
    @76
    @78
    @80
    w3a
    @45
    cV
    @46
    cP
    cJ
    cX
    cA
    pi1co.p
    wph
    @16
    @44
    pi1co.j
    adantr
    #
    wph
    @17
    @44
    pi1co.a
    adantr
    @31
    @45
    pi1co.v
    a1i
    pi1eluni
    biimpa
    #
    simp1d
    #
    @54
    @71
    cA
    @77
    @45
    @72
    @53
    @45
    @68
    @70
    @72
    @73
    simp3d
    #
    adantr
    @54
    @76
    @78
    @80
    @82
    simp2d
    #
    eqtr4d
    #
    wph
    @22
    @44
    @53
    pi1co.f
    ad2antrr
    #
    copco
    eceq1d
    @45
    @53
    @55
    @27
    wcel
    #
    @57
    @65
    wceq
    #
    @54
    @88
    @55
    @67
    wcel
    cc0
    @55
    cfv
    #
    cA
    wceq
    c1
    @55
    cfv
    #
    cA
    wceq
    @54
    @34
    @46
    cJ
    @75
    @83
    @86
    pcocn
    @54
    @90
    @69
    cA
    @54
    @34
    @46
    cJ
    @75
    @83
    pco0
    @45
    @70
    @53
    @45
    @68
    @70
    @72
    @73
    simp2d
    #
    adantr
    eqtrd
    @54
    @91
    @79
    cA
    @54
    @34
    @46
    cJ
    @75
    @83
    pco1
    @54
    @76
    @78
    @80
    @82
    simp3d
    #
    eqtrd
    @54
    cV
    @55
    cP
    cJ
    cX
    cA
    pi1co.p
    wph
    @16
    @44
    @53
    pi1co.j
    ad2antrr
    #
    wph
    @17
    @44
    @53
    pi1co.a
    ad2antrr
    #
    @31
    @54
    pi1co.v
    a1i
    pi1eluni
    mpbir3and
    wph
    @88
    @89
    @44
    wph
    cA
    cB
    cP
    cQ
    @55
    vg
    cF
    cG
    cJ
    cK
    cV
    cX
    pi1co.p
    pi1co.q
    pi1co.v
    pi1co.g
    pi1co.j
    pi1co.f
    pi1co.a
    pi1co.b
    pi1coval
    adantlr
    syldan
    @54
    @2
    @11
    cQ
    cK
    @58
    @61
    @18
    cB
    pi1co.q
    @2
    eqid
    #
    wph
    @19
    @44
    @53
    @23
    ad2antrr
    wph
    @20
    @44
    @53
    @25
    ad2antrr
    @11
    eqid
    #
    @45
    @58
    @2
    cuni
    #
    wcel
    #
    @53
    @45
    @99
    @58
    cii
    cK
    ccn
    co
    #
    wcel
    #
    cc0
    @58
    cfv
    #
    cB
    wceq
    c1
    @58
    cfv
    #
    cB
    wceq
    @45
    @68
    @22
    @101
    @74
    wph
    @22
    @44
    pi1co.f
    adantr
    @34
    cF
    cii
    cJ
    cK
    cnco
    syl2anc
    @45
    @102
    @69
    cF
    cfv
    #
    @24
    cB
    @45
    cc0
    c1
    cicc
    co
    #
    cX
    @34
    wf
    #
    cc0
    @105
    wcel
    #
    @102
    @104
    wceq
    @45
    cii
    @105
    ctopon
    cfv
    wcel
    #
    @16
    @68
    @106
    @108
    @45
    iitopon
    a1i
    @81
    @74
    @34
    cii
    cJ
    @105
    cX
    cnf2
    syl3anc
    #
    0elunit
    @105
    cX
    cc0
    cF
    @34
    fvco3
    sylancl
    @45
    @69
    cA
    cF
    @92
    fveq2d
    wph
    @24
    cB
    wceq
    #
    @44
    pi1co.b
    adantr
    #
    3eqtrd
    @45
    @103
    @71
    cF
    cfv
    #
    @24
    cB
    @45
    @106
    c1
    @105
    wcel
    #
    @103
    @112
    wceq
    @109
    1elunit
    @105
    cX
    c1
    cF
    @34
    fvco3
    sylancl
    @45
    @71
    cA
    cF
    @84
    fveq2d
    @111
    3eqtrd
    @45
    @2
    @58
    cQ
    cK
    @18
    cB
    pi1co.q
    wph
    @19
    @44
    @23
    adantr
    wph
    @20
    @44
    @25
    adantr
    @45
    @2
    eqidd
    pi1eluni
    mpbir3and
    adantr
    @54
    @61
    @98
    wcel
    #
    @61
    @100
    wcel
    #
    cc0
    @61
    cfv
    #
    cB
    wceq
    #
    c1
    @61
    cfv
    #
    cB
    wceq
    #
    @54
    @76
    @22
    @115
    @83
    @87
    @46
    cF
    cii
    cJ
    cK
    cnco
    syl2anc
    @54
    @116
    @77
    cF
    cfv
    #
    @24
    cB
    @54
    @105
    cX
    @46
    wf
    #
    @107
    @116
    @120
    wceq
    @54
    @108
    @16
    @76
    @121
    @108
    @54
    iitopon
    a1i
    @94
    @83
    @46
    cii
    cJ
    @105
    cX
    cnf2
    syl3anc
    #
    0elunit
    @105
    cX
    cc0
    cF
    @46
    fvco3
    sylancl
    @54
    @77
    cA
    cF
    @85
    fveq2d
    wph
    @110
    @44
    @53
    pi1co.b
    ad2antrr
    #
    3eqtrd
    @54
    @118
    @79
    cF
    cfv
    #
    @24
    cB
    @54
    @121
    @113
    @118
    @124
    wceq
    @122
    1elunit
    @105
    cX
    c1
    cF
    @46
    fvco3
    sylancl
    @54
    @79
    cA
    cF
    @93
    fveq2d
    @123
    3eqtrd
    wph
    @114
    @115
    @117
    @119
    w3a
    wb
    @44
    @53
    wph
    @2
    @61
    cQ
    cK
    @18
    cB
    pi1co.q
    @23
    @25
    wph
    @2
    eqidd
    pi1eluni
    ad2antrr
    mpbir3and
    pi1addval
    3eqtr4d
    @54
    @48
    @56
    cG
    @54
    cV
    @6
    cP
    cJ
    @34
    @46
    cX
    cA
    pi1co.p
    pi1co.v
    @94
    @95
    @6
    eqid
    #
    wph
    @44
    @53
    simplr
    @45
    @53
    simpr
    pi1addval
    fveq2d
    @54
    @38
    @60
    @50
    @62
    @11
    @45
    @38
    @60
    wceq
    @53
    wph
    cA
    cB
    cP
    cQ
    @34
    vg
    cF
    cG
    cJ
    cK
    cV
    cX
    pi1co.p
    pi1co.q
    pi1co.v
    pi1co.g
    pi1co.j
    pi1co.f
    pi1co.a
    pi1co.b
    pi1coval
    adantr
    wph
    @53
    @50
    @62
    wceq
    @44
    wph
    cA
    cB
    cP
    cQ
    @46
    vg
    cF
    cG
    cJ
    cK
    cV
    cX
    pi1co.p
    pi1co.q
    pi1co.v
    pi1co.g
    pi1co.j
    pi1co.f
    pi1co.a
    pi1co.b
    pi1coval
    adantlr
    oveq12d
    3eqtr4d
    ectocld
    ralrimiva
    @45
    @40
    vz
    cV
    @29
    wph
    cV
    @29
    wceq
    @44
    @33
    adantr
    raleqdv
    mpbird
    ectocld
    syldan
    ralrimiva
    jca
    vz
    vy
    @6
    @11
    cP
    cQ
    cG
    cV
    @2
    pi1co.v
    @96
    @125
    @97
    isghm
    sylanbrc
end
