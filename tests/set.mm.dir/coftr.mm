include "cv.mm"
include "wf.mm"
include "wsmo.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "fdm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "syl.mm"
include "ad2antrl.mm"
include "word.mm"
include "wfn.mm"
include "ffn.mm"
include "smodm2.mm"
include "sylan.mm"
include "3adant3.mm"
include "adantr.mm"
include "simpl3.mm"
include "simprl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "ffvelrn.mm"
include "3ad2antl3.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "sylc.mm"
include "con0.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "ordsson.mm"
include "syl5ss.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "rabn0.mm"
include "sylibr.mm"
include "oninton.mm"
include "syl2an.mm"
include "eloni.mm"
include "simpl.mm"
include "intminss.mm"
include "adantl.mm"
include "ordtr2.mm"
include "imp.mm"
include "syl22anc.mm"
include "rexlimdvaa.mm"
include "fmptd.mm"
include "syl3anc.mm"
include "simprr.mm"
include "syl5.mm"
include "expdimp.mm"
include "syl2anc.mm"
include "simpr.mm"
include "jca.mm"
include "elrab.mm"
include "sstr2.mm"
include "smoword.mm"
include "biimprd.mm"
include "syl9r.mm"
include "expr.mm"
include "com23.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ssint.mm"
include "fvmptg.mm"
include "syl5ibrcom.mm"
include "ex.mm"
include "reximdvai.mm"
include "ancoms.mm"
include "syl32anc.mm"
include "mpdd.mm"
include "feq1.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "3impib.mm"
include "exlimdv.mm"
include "exlimiv.mm"

theorem coftr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vn: setvar n
  let cH: class H
  let vs: setvar s
  assume coftr.1: |- H = ( t e. C |-> |^| { n e. B | ( g ` t ) C_ ( f ` n ) } )

  disjoint A f
  disjoint A g
  disjoint A s
  disjoint A w
  disjoint A x
  disjoint f g
  disjoint f s
  disjoint f w
  disjoint f x
  disjoint g s
  disjoint g w
  disjoint g x
  disjoint s w
  disjoint s x
  disjoint w x
  disjoint A z
  disjoint f z
  disjoint g z
  disjoint s z
  disjoint w z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B w
  disjoint f h
  disjoint g h
  disjoint h s
  disjoint h w
  disjoint B n
  disjoint B t
  disjoint f n
  disjoint f t
  disjoint g n
  disjoint g t
  disjoint n t
  disjoint n w
  disjoint t w
  disjoint B x
  disjoint B y
  disjoint f y
  disjoint g y
  disjoint s y
  disjoint w y
  disjoint x y
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C s
  disjoint C w
  disjoint C t
  disjoint C z
  disjoint H h
  disjoint H s
  disjoint H w
  disjoint n y
  assert |- ( E. f ( f : B --> A /\ Smo f /\ A. x e. A E. y e. B x C_ ( f ` y ) ) -> ( E. g ( g : C --> A /\ A. z e. A E. w e. C z C_ ( g ` w ) ) -> E. h ( h : C --> B /\ A. s e. B E. w e. C s C_ ( h ` w ) ) ) )

  proof
    cB
    cA
    vf
    cv
    #
    wf
    #
    @0
    wsmo
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cfv
    #
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    w3a
    #
    cC
    cA
    vg
    cv
    #
    wf
    #
    vz
    cv
    #
    vw
    cv
    #
    @10
    cfv
    #
    wss
    #
    vw
    cC
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    vg
    wex
    cC
    cB
    vh
    cv
    #
    wf
    #
    vs
    cv
    #
    @13
    @19
    cfv
    #
    wss
    #
    vw
    cC
    wrex
    #
    vs
    cB
    wral
    #
    wa
    #
    vh
    wex
    #
    wi
    vf
    @9
    @18
    @27
    vg
    @9
    @18
    @27
    @9
    @18
    wa
    #
    cH
    cvv
    wcel
    #
    cC
    cB
    cH
    wf
    #
    @21
    @13
    cH
    cfv
    #
    wss
    #
    vw
    cC
    wrex
    #
    vs
    cB
    wral
    #
    @27
    @11
    @29
    @9
    @17
    @11
    cC
    cvv
    wcel
    #
    @29
    @11
    cC
    @10
    cdm
    cvv
    cC
    cA
    @10
    fdm
    @10
    vg
    vex
    dmex
    syl6eqelr
    @35
    cH
    vw
    cC
    @14
    vn
    cv
    #
    @0
    cfv
    #
    wss
    #
    vn
    cB
    crab
    #
    cint
    #
    cmpt
    #
    cvv
    cH
    vt
    cC
    vt
    cv
    #
    @10
    cfv
    #
    @37
    wss
    #
    vn
    cB
    crab
    #
    cint
    #
    cmpt
    @41
    coftr.1
    vt
    vw
    cC
    @46
    @40
    @42
    @13
    wceq
    #
    @45
    @39
    @47
    @44
    @38
    vn
    cB
    @47
    @43
    @14
    @37
    @42
    @13
    @10
    fveq2
    sseq1d
    rabbidv
    inteqd
    #
    cbvmptv
    eqtri
    #
    vw
    cC
    @40
    cvv
    mptexg
    syl5eqel
    syl
    ad2antrl
    @28
    cB
    word
    #
    @8
    @11
    @30
    @9
    @50
    @18
    @1
    @2
    @50
    @8
    @1
    @0
    cB
    wfn
    #
    @2
    @50
    cB
    cA
    @0
    ffn
    #
    cB
    @0
    smodm2
    sylan
    3adant3
    adantr
    #
    @1
    @2
    @8
    @18
    simpl3
    #
    @9
    @11
    @17
    simprl
    #
    @50
    @8
    @11
    w3a
    #
    vw
    cC
    @40
    cB
    cH
    @56
    @13
    cC
    wcel
    #
    wa
    #
    @50
    @14
    @5
    wss
    #
    vy
    cB
    wrex
    #
    @40
    cB
    wcel
    #
    @50
    @8
    @11
    @57
    simpl1
    @58
    @8
    @14
    cA
    wcel
    #
    @60
    @50
    @8
    @11
    @57
    simpl2
    @11
    @50
    @57
    @62
    @8
    cC
    cA
    @13
    @10
    ffvelrn
    3ad2antl3
    @7
    @60
    vx
    @14
    cA
    @3
    @14
    wceq
    @6
    @59
    vy
    cB
    @3
    @14
    @5
    sseq1
    rexbidv
    rspccv
    sylc
    @50
    @59
    @61
    vy
    cB
    @50
    @4
    cB
    wcel
    #
    @59
    wa
    #
    wa
    #
    @40
    word
    #
    @50
    @40
    @4
    wss
    #
    @63
    @61
    @65
    @40
    con0
    wcel
    #
    @66
    @50
    @39
    con0
    wss
    @39
    c0
    wne
    #
    @68
    @64
    @50
    @39
    cB
    con0
    @38
    vn
    cB
    ssrab2
    cB
    ordsson
    syl5ss
    @64
    @38
    vn
    cB
    wrex
    @69
    @38
    @59
    vn
    @4
    cB
    @36
    @4
    wceq
    @37
    @5
    @14
    @36
    @4
    @0
    fveq2
    sseq2d
    #
    rspcev
    @38
    vn
    cB
    rabn0
    sylibr
    @39
    oninton
    syl2an
    @40
    eloni
    syl
    @50
    @64
    simpl
    @64
    @67
    @50
    @38
    @59
    vn
    @4
    cB
    @70
    intminss
    adantl
    @50
    @63
    @59
    simprl
    @66
    @50
    wa
    @67
    @63
    wa
    @61
    @40
    @4
    cB
    ordtr2
    imp
    syl22anc
    rexlimdvaa
    sylc
    #
    @49
    fmptd
    syl3anc
    @28
    @33
    vs
    cB
    @28
    @21
    cB
    wcel
    #
    @21
    @0
    cfv
    #
    @14
    wss
    #
    vw
    cC
    wrex
    #
    @33
    @28
    @17
    @1
    @72
    @75
    wi
    @9
    @11
    @17
    simprr
    @1
    @2
    @8
    @18
    simpl1
    #
    @17
    @1
    @72
    @75
    @1
    @72
    wa
    @73
    cA
    wcel
    @17
    @75
    cB
    cA
    @21
    @0
    ffvelrn
    @16
    @75
    vz
    @73
    cA
    @12
    @73
    wceq
    @15
    @74
    vw
    cC
    @12
    @73
    @14
    sseq1
    rexbidv
    rspccv
    syl5
    expdimp
    syl2anc
    @28
    @50
    @8
    @11
    @51
    @2
    @72
    @75
    @33
    wi
    #
    wi
    @53
    @54
    @55
    @28
    @1
    @51
    @76
    @52
    syl
    @1
    @2
    @8
    @18
    simpl2
    @56
    @51
    @2
    wa
    #
    @72
    @77
    @78
    @72
    wa
    #
    @56
    @77
    @79
    @56
    wa
    @74
    @32
    vw
    cC
    @79
    @56
    @57
    @74
    @32
    wi
    @79
    @74
    @58
    @32
    @79
    @74
    @58
    @32
    wi
    @58
    @57
    @61
    wa
    #
    @79
    @74
    wa
    #
    @32
    @58
    @57
    @61
    @56
    @57
    simpr
    @71
    jca
    @81
    @32
    @80
    @21
    @40
    wss
    #
    @81
    @21
    @4
    wss
    #
    vy
    @39
    wral
    @82
    @81
    @83
    vy
    @39
    @4
    @39
    wcel
    @64
    @81
    @83
    @38
    @59
    vn
    @4
    cB
    @70
    elrab
    @79
    @74
    @63
    @59
    @83
    @79
    @63
    @74
    @59
    @83
    wi
    #
    @78
    @72
    @63
    @74
    @84
    wi
    @74
    @59
    @73
    @5
    wss
    #
    @78
    @72
    @63
    wa
    wa
    #
    @83
    @73
    @14
    @5
    sstr2
    @86
    @83
    @85
    cB
    @21
    @4
    @0
    smoword
    biimprd
    syl9r
    expr
    com23
    imp4b
    syl5bi
    ralrimiv
    vy
    @21
    @39
    ssint
    sylibr
    @80
    @31
    @40
    @21
    vt
    @13
    @46
    @40
    cC
    cB
    cH
    @48
    coftr.1
    fvmptg
    sseq2d
    syl5ibrcom
    syl5
    ex
    com23
    expdimp
    reximdvai
    ancoms
    expr
    syl32anc
    mpdd
    ralrimiv
    @29
    @30
    @34
    @27
    @26
    @30
    @34
    wa
    vh
    cH
    cvv
    @19
    cH
    wceq
    #
    @20
    @30
    @25
    @34
    cC
    cB
    @19
    cH
    feq1
    @87
    @24
    @33
    vs
    cB
    @87
    @23
    @32
    vw
    cC
    @87
    @22
    @31
    @21
    @13
    @19
    cH
    fveq1
    sseq2d
    rexbidv
    ralbidv
    anbi12d
    spcegv
    3impib
    syl3anc
    ex
    exlimdv
    exlimiv
end
