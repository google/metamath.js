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
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cii.mm"
include "ccn.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "0elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "pi1grp.mm"
include "syl2anc.mm"
include "1elunit.mm"
include "jca.mm"
include "w3a.mm"
include "pcorevcl.mm"
include "syl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "eqcomd.mm"
include "simp3d.mm"
include "pi1xfrf.mm"
include "cuni.mm"
include "cphtpc.mm"
include "cqs.mm"
include "pi1bas2.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "cec.mm"
include "eqid.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "adantlr.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cpco.mm"
include "wer.mm"
include "phtpcer.mm"
include "pi1eluni.mm"
include "3adant3.mm"
include "wb.mm"
include "adantr.mm"
include "biimp3a.mm"
include "pco0.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "pcocn.mm"
include "3ad2ant1.mm"
include "3eqtr4rd.mm"
include "erref.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "c4.mm"
include "cmul.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt.mm"
include "pcoass.mm"
include "csn.mm"
include "cxp.mm"
include "pco1.mm"
include "pcorev2.mm"
include "pcohtpy.mm"
include "pcopt.mm"
include "ertrd.mm"
include "ertr3d.mm"
include "ertr4d.mm"
include "erthi.mm"
include "mpbir3and.mm"
include "pi1xfrval.mm"
include "eqidd.mm"
include "pi1addval.mm"
include "3eqtr4d.mm"
include "simp2.mm"
include "simp3.mm"
include "simpr.mm"
include "oveq12d.mm"
include "3expa.mm"
include "ectocld.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "isghm.mm"
include "sylanbrc.mm"

theorem pi1xfr
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vs: setvar s
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cH: class H
  assume pi1xfr.p: |- P = ( J pi1 ( F ` 0 ) )
  assume pi1xfr.q: |- Q = ( J pi1 ( F ` 1 ) )
  assume pi1xfr.b: |- B = ( Base ` P )
  assume pi1xfr.g: |- G = ran ( g e. U. B |-> <. [ g ] ( ~=ph ` J ) , [ ( I ( *p ` J ) ( g ( *p ` J ) F ) ) ] ( ~=ph ` J ) >. )
  assume pi1xfr.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1xfr.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1xfr.i: |- I = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )

  disjoint g x
  disjoint B g
  disjoint B x
  disjoint F g
  disjoint F x
  disjoint I g
  disjoint I x
  disjoint g ph
  disjoint ph x
  disjoint J g
  disjoint J x
  disjoint P g
  disjoint P x
  disjoint Q g
  disjoint Q x
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g y
  disjoint g z
  disjoint h s
  disjoint h u
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F h
  disjoint F s
  disjoint F u
  disjoint F y
  disjoint F z
  disjoint I h
  disjoint I s
  disjoint I u
  disjoint I y
  disjoint I z
  disjoint A g
  disjoint A s
  disjoint A x
  disjoint G f
  disjoint G h
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H s
  disjoint H z
  disjoint f ph
  disjoint h ph
  disjoint ph s
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J h
  disjoint J s
  disjoint J u
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P h
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint Q f
  disjoint Q h
  disjoint Q s
  disjoint Q y
  disjoint Q z
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
    cB
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
    cB
    wral
    #
    vy
    cB
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
    cc0
    cF
    cfv
    #
    cX
    wcel
    #
    @0
    pi1xfr.j
    wph
    cc0
    c1
    cicc
    co
    #
    cX
    cF
    wf
    #
    cc0
    @19
    wcel
    @18
    wph
    cii
    @19
    ctopon
    cfv
    wcel
    #
    @16
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @20
    @21
    wph
    iitopon
    a1i
    pi1xfr.j
    pi1xfr.f
    cF
    cii
    cJ
    @19
    cX
    cnf2
    syl3anc
    #
    0elunit
    @19
    cX
    cc0
    cF
    ffvelrn
    sylancl
    #
    cP
    cJ
    cX
    @17
    pi1xfr.p
    pi1grp
    syl2anc
    wph
    @16
    c1
    cF
    cfv
    #
    cX
    wcel
    #
    @1
    pi1xfr.j
    wph
    @20
    c1
    @19
    wcel
    @27
    @24
    1elunit
    @19
    cX
    c1
    cF
    ffvelrn
    sylancl
    #
    cQ
    cJ
    cX
    @26
    pi1xfr.q
    pi1grp
    syl2anc
    jca
    wph
    @3
    @15
    wph
    cB
    cP
    cQ
    vg
    cF
    cG
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    pi1xfr.j
    pi1xfr.f
    wph
    cI
    @22
    wcel
    #
    cc0
    cI
    cfv
    #
    @26
    wceq
    #
    c1
    cI
    cfv
    #
    @17
    wceq
    #
    wph
    @23
    @29
    @31
    @33
    w3a
    pi1xfr.f
    vx
    cF
    cI
    cJ
    pi1xfr.i
    pcorevcl
    syl
    #
    simp1d
    #
    wph
    @30
    @26
    wph
    @29
    @31
    @33
    @34
    simp2d
    #
    eqcomd
    #
    wph
    @29
    @31
    @33
    @34
    simp3d
    #
    pi1xfrf
    wph
    @14
    vy
    cB
    wph
    @4
    cB
    wcel
    #
    @4
    cB
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
    @39
    @43
    wph
    cB
    @42
    @4
    wph
    cB
    cP
    cJ
    cX
    @17
    pi1xfr.p
    pi1xfr.j
    @25
    cB
    cP
    cbs
    cfv
    wceq
    wph
    pi1xfr.b
    a1i
    #
    pi1bas2
    #
    eleq2d
    biimpa
    vf
    cv
    #
    @41
    cec
    #
    @5
    @6
    co
    #
    cG
    cfv
    #
    @47
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
    cB
    wral
    @14
    wph
    vf
    @4
    @40
    @41
    @42
    @42
    eqid
    #
    @47
    @4
    wceq
    #
    @52
    @13
    vz
    cB
    @54
    @49
    @8
    @51
    @12
    @54
    @48
    @7
    cG
    @47
    @4
    @5
    @6
    oveq1
    fveq2d
    @54
    @50
    @9
    @10
    @11
    @47
    @4
    cG
    fveq2
    oveq1d
    eqeq12d
    ralbidv
    wph
    @46
    @40
    wcel
    #
    wa
    #
    @52
    vz
    cB
    @56
    @5
    cB
    wcel
    #
    @5
    @42
    wcel
    #
    @52
    wph
    @57
    @58
    @55
    wph
    @57
    @58
    wph
    cB
    @42
    @5
    @45
    eleq2d
    biimpa
    adantlr
    @47
    vh
    cv
    #
    @41
    cec
    #
    @6
    co
    #
    cG
    cfv
    #
    @50
    @60
    cG
    cfv
    #
    @11
    co
    #
    wceq
    #
    @52
    @56
    vh
    @5
    @40
    @41
    @42
    @53
    @60
    @5
    wceq
    #
    @62
    @49
    @64
    @51
    @66
    @61
    @48
    cG
    @60
    @5
    @47
    @6
    oveq2
    fveq2d
    @66
    @63
    @10
    @50
    @11
    @60
    @5
    cG
    fveq2
    oveq2d
    eqeq12d
    wph
    @55
    @59
    @40
    wcel
    #
    @65
    wph
    @55
    @67
    w3a
    #
    @46
    @59
    cJ
    cpco
    cfv
    #
    co
    #
    @41
    cec
    #
    cG
    cfv
    #
    cI
    @46
    cF
    @69
    co
    #
    @69
    co
    #
    @41
    cec
    #
    cI
    @59
    cF
    @69
    co
    #
    @69
    co
    #
    @41
    cec
    #
    @11
    co
    #
    @62
    @64
    @68
    cI
    @70
    cF
    @69
    co
    #
    @69
    co
    #
    @41
    cec
    @74
    @77
    @69
    co
    #
    @41
    cec
    @72
    @79
    @68
    @81
    @82
    @41
    @22
    @22
    @41
    wer
    @68
    cJ
    phtpcer
    a1i
    #
    @68
    @81
    cI
    @73
    @77
    @69
    co
    #
    @69
    co
    @82
    @41
    @22
    @83
    @68
    cI
    @80
    cI
    cJ
    @84
    @68
    cc0
    @70
    cfv
    #
    @17
    cc0
    @80
    cfv
    @32
    @68
    @85
    cc0
    @46
    cfv
    #
    @17
    @68
    @46
    @59
    cJ
    wph
    @55
    @46
    @22
    wcel
    #
    @67
    @56
    @87
    @86
    @17
    wceq
    #
    c1
    @46
    cfv
    #
    @17
    wceq
    #
    wph
    @55
    @87
    @88
    @90
    w3a
    wph
    cB
    @46
    cP
    cJ
    cX
    @17
    pi1xfr.p
    pi1xfr.j
    @25
    @44
    pi1eluni
    biimpa
    #
    simp1d
    #
    3adant3
    #
    @68
    @59
    @22
    wcel
    #
    cc0
    @59
    cfv
    #
    @17
    wceq
    #
    c1
    @59
    cfv
    #
    @17
    wceq
    #
    wph
    @55
    @67
    @94
    @96
    @98
    w3a
    #
    wph
    @67
    @99
    wb
    @55
    wph
    cB
    @59
    cP
    cJ
    cX
    @17
    pi1xfr.p
    pi1xfr.j
    @25
    @44
    pi1eluni
    adantr
    biimp3a
    #
    simp1d
    #
    pco0
    wph
    @55
    @88
    @67
    @56
    @87
    @88
    @90
    @91
    simp2d
    #
    3adant3
    eqtrd
    #
    @68
    @70
    cF
    cJ
    @68
    @46
    @59
    cJ
    @93
    @101
    @68
    @89
    @17
    @95
    wph
    @55
    @90
    @67
    @56
    @87
    @88
    @90
    @91
    simp3d
    #
    3adant3
    #
    @68
    @94
    @96
    @98
    @100
    simp2d
    #
    eqtr4d
    #
    pcocn
    #
    wph
    @55
    @23
    @67
    pi1xfr.f
    3ad2ant1
    #
    pco0
    wph
    @55
    @33
    @67
    @38
    3ad2ant1
    #
    3eqtr4rd
    @68
    cI
    @41
    @22
    @83
    wph
    @55
    @29
    @67
    @35
    3ad2ant1
    #
    erref
    @68
    @80
    @46
    @76
    @69
    co
    #
    @84
    @41
    @22
    @83
    @68
    vu
    vu
    @19
    vu
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    @113
    c1
    c4
    cdiv
    co
    #
    cle
    wbr
    c2
    @113
    cmul
    co
    @113
    @115
    caddc
    co
    cif
    @113
    c2
    cdiv
    co
    @114
    caddc
    co
    cif
    cmpt
    #
    @46
    @59
    cF
    cJ
    @93
    @101
    @109
    @107
    @68
    @94
    @96
    @98
    @100
    simp3d
    #
    @116
    eqid
    #
    pcoass
    @68
    @112
    @46
    cF
    @77
    @69
    co
    #
    @69
    co
    @84
    @41
    @22
    @83
    @68
    @46
    @76
    @46
    cJ
    @119
    @68
    @89
    @95
    cc0
    @76
    cfv
    #
    @107
    @68
    @59
    cF
    cJ
    @101
    @109
    pco0
    #
    eqtr4d
    @68
    @46
    @41
    @22
    @83
    @93
    erref
    @68
    @76
    cF
    cI
    @69
    co
    #
    @76
    @69
    co
    #
    @119
    @41
    @22
    @83
    @68
    @123
    @19
    @17
    csn
    cxp
    #
    @76
    @69
    co
    #
    @76
    @41
    @22
    @83
    @68
    @122
    @76
    @124
    cJ
    @76
    @68
    c1
    @122
    cfv
    @32
    @120
    @68
    cF
    cI
    cJ
    @109
    @111
    pco1
    @68
    @95
    @17
    @120
    @32
    @106
    @121
    @110
    3eqtr4rd
    #
    eqtrd
    @68
    @23
    @122
    @124
    @41
    wbr
    @109
    vx
    @124
    cF
    cI
    cJ
    pi1xfr.i
    @124
    eqid
    #
    pcorev2
    syl
    @68
    @76
    @41
    @22
    @83
    @68
    @59
    cF
    cJ
    @101
    @109
    @117
    pcocn
    #
    erref
    pcohtpy
    @68
    @76
    @22
    wcel
    @120
    @17
    wceq
    @125
    @76
    @41
    wbr
    @128
    @68
    @120
    @95
    @17
    @121
    @106
    eqtrd
    @124
    @76
    cJ
    @17
    @127
    pcopt
    syl2anc
    ertrd
    @68
    vu
    @116
    cF
    cI
    @76
    cJ
    @109
    @111
    @128
    @68
    @30
    @26
    wph
    @55
    @31
    @67
    @36
    3ad2ant1
    #
    eqcomd
    #
    @126
    @118
    pcoass
    ertr3d
    pcohtpy
    @68
    vu
    @116
    @46
    cF
    @77
    cJ
    @93
    @109
    @68
    cI
    @76
    cJ
    @111
    @128
    @126
    pcocn
    #
    @105
    @68
    cc0
    @77
    cfv
    #
    @26
    @68
    @132
    @30
    @26
    @68
    cI
    @76
    cJ
    @111
    @128
    pco0
    @129
    eqtrd
    #
    eqcomd
    @118
    pcoass
    ertr4d
    ertrd
    pcohtpy
    @68
    vu
    @116
    cI
    @73
    @77
    cJ
    @111
    wph
    @55
    @73
    @22
    wcel
    @67
    @56
    @46
    cF
    cJ
    @92
    wph
    @23
    @55
    pi1xfr.f
    adantr
    #
    @104
    pcocn
    #
    3adant3
    @131
    wph
    @55
    @32
    cc0
    @73
    cfv
    #
    wceq
    @67
    @56
    @86
    @17
    @136
    @32
    @102
    @56
    @46
    cF
    cJ
    @92
    @134
    pco0
    wph
    @33
    @55
    @38
    adantr
    #
    3eqtr4rd
    #
    3adant3
    @68
    c1
    @73
    cfv
    #
    @26
    @132
    @68
    @46
    cF
    cJ
    @93
    @109
    pco1
    @133
    eqtr4d
    @118
    pcoass
    ertr4d
    erthi
    @68
    @70
    cB
    cP
    cQ
    vg
    cF
    cG
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    wph
    @55
    @16
    @67
    pi1xfr.j
    3ad2ant1
    #
    @109
    @111
    @130
    @110
    @68
    @70
    @40
    wcel
    #
    @70
    @22
    wcel
    #
    @85
    @17
    wceq
    #
    c1
    @70
    cfv
    #
    @17
    wceq
    #
    @108
    @103
    @68
    @144
    @97
    @17
    @68
    @46
    @59
    cJ
    @93
    @101
    pco1
    @117
    eqtrd
    wph
    @55
    @141
    @142
    @143
    @145
    w3a
    wb
    @67
    wph
    cB
    @70
    cP
    cJ
    cX
    @17
    pi1xfr.p
    pi1xfr.j
    @25
    @44
    pi1eluni
    3ad2ant1
    mpbir3and
    pi1xfrval
    @68
    @2
    @11
    cQ
    cJ
    @74
    @77
    cX
    @26
    pi1xfr.q
    @2
    eqid
    #
    @140
    wph
    @55
    @27
    @67
    @28
    3ad2ant1
    #
    @11
    eqid
    #
    @68
    @74
    @2
    cuni
    #
    wcel
    @74
    @22
    wcel
    #
    cc0
    @74
    cfv
    #
    @26
    wceq
    #
    c1
    @74
    cfv
    #
    @26
    wceq
    #
    wph
    @55
    @150
    @67
    @56
    cI
    @73
    cJ
    wph
    @29
    @55
    @35
    adantr
    #
    @135
    @138
    pcocn
    3adant3
    wph
    @55
    @152
    @67
    @56
    @151
    @30
    @26
    @56
    cI
    @73
    cJ
    @155
    @135
    pco0
    wph
    @31
    @55
    @36
    adantr
    eqtrd
    3adant3
    wph
    @55
    @154
    @67
    @56
    @153
    @139
    @26
    @56
    cI
    @73
    cJ
    @155
    @135
    pco1
    @56
    @46
    cF
    cJ
    @92
    @134
    pco1
    eqtrd
    3adant3
    @68
    @2
    @74
    cQ
    cJ
    cX
    @26
    pi1xfr.q
    @140
    @147
    @68
    @2
    eqidd
    #
    pi1eluni
    mpbir3and
    @68
    @77
    @149
    wcel
    @77
    @22
    wcel
    @132
    @26
    wceq
    c1
    @77
    cfv
    #
    @26
    wceq
    @131
    @133
    @68
    @157
    c1
    @76
    cfv
    @26
    @68
    cI
    @76
    cJ
    @111
    @128
    pco1
    @68
    @59
    cF
    cJ
    @101
    @109
    pco1
    eqtrd
    @68
    @2
    @77
    cQ
    cJ
    cX
    @26
    pi1xfr.q
    @140
    @147
    @156
    pi1eluni
    mpbir3and
    pi1addval
    3eqtr4d
    @68
    @61
    @71
    cG
    @68
    cB
    @6
    cP
    cJ
    @46
    @59
    cX
    @17
    pi1xfr.p
    pi1xfr.b
    @140
    wph
    @55
    @18
    @67
    @25
    3ad2ant1
    @6
    eqid
    #
    wph
    @55
    @67
    simp2
    wph
    @55
    @67
    simp3
    #
    pi1addval
    fveq2d
    @68
    @50
    @75
    @63
    @78
    @11
    wph
    @55
    @50
    @75
    wceq
    @67
    @56
    @46
    cB
    cP
    cQ
    vg
    cF
    cG
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    wph
    @16
    @55
    pi1xfr.j
    adantr
    @134
    @155
    wph
    @26
    @30
    wceq
    @55
    @37
    adantr
    @137
    wph
    @55
    simpr
    pi1xfrval
    3adant3
    @68
    @59
    cB
    cP
    cQ
    vg
    cF
    cG
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    @140
    @109
    @111
    @130
    @110
    @159
    pi1xfrval
    oveq12d
    3eqtr4d
    3expa
    ectocld
    syldan
    ralrimiva
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
    cB
    @2
    pi1xfr.b
    @146
    @158
    @148
    isghm
    sylanbrc
end
