include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "wcel.mm"
include "cv.mm"
include "cioo.mm"
include "co.mm"
include "cixp.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "cbl.mm"
include "cmopn.mm"
include "cr.mm"
include "cmap.mm"
include "cxmt.mm"
include "cxr.mm"
include "rrndsxmet.mm"
include "cvv.mm"
include "nfv.mm"
include "reex.mm"
include "a1i.mm"
include "ioossre.mm"
include "ixpssmapc.mm"
include "sseldd.mm"
include "crp.mm"
include "clt.mm"
include "cinf.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "simpr.mm"
include "fvixp2.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "resubcld.mm"
include "cc0.mm"
include "rexrd.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "posdifd.mm"
include "mpbid.mm"
include "elrpd.mm"
include "ioogtlb.mm"
include "ifcld.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "eqsstrd.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "ltso.mm"
include "rnmptfi.mm"
include "syl5eqel.mm"
include "elexd.mm"
include "rnmptn0.mm"
include "eqnetrd.mm"
include "rpssre.mm"
include "sstrd.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "rpxr.mm"
include "blopn.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "rrxtopnfi.mm"
include "eqcomi.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "cpsmet.mm"
include "xmetpsmet.mm"
include "blcntrps.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "w3a.mm"
include "wfn.mm"
include "elmapfn.mm"
include "3ad2ant2.mm"
include "3ad2antl1.mm"
include "simpl2.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrnd.mm"
include "infxrrefi.mm"
include "ressxr.mm"
include "elrnmpt1.mm"
include "syl6eleqr.mm"
include "infxrlb.mm"
include "eqbrtrd.mm"
include "min2.mm"
include "letrd.mm"
include "lesubd.mm"
include "adantlr.mm"
include "adantll.mm"
include "3adantl3.mm"
include "cme.mm"
include "rrndsmet.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "metcl.mm"
include "cabs.mm"
include "recnd.mm"
include "abscld.mm"
include "leabsd.mm"
include "cds.mm"
include "ciun.mm"
include "ixpf.mm"
include "iunss.mm"
include "sylibr.mm"
include "fssd.mm"
include "rrnprjdstle.mm"
include "rrxdsfi.mm"
include "oveqd.mm"
include "breqtrd.mm"
include "simpl3.mm"
include "lelttrd.mm"
include "wb.mm"
include "ltsub23.mm"
include "caddc.mm"
include "readdcld.mm"
include "abssubd.mm"
include "ltsubadd2d.mm"
include "min1.mm"
include "leaddsub2d.mm"
include "ltletrd.mm"
include "eliood.mm"
include "jca.mm"
include "vex.mm"
include "elixp.mm"
include "ballss3.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem ioorrnopnlem
  let wph: wff ph
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cH: class H
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume ioorrnopnlem.x: |- ( ph -> X e. Fin )
  assume ioorrnopnlem.n: |- ( ph -> X =/= (/) )
  assume ioorrnopnlem.a: |- ( ph -> A : X --> RR )
  assume ioorrnopnlem.b: |- ( ph -> B : X --> RR )
  assume ioorrnopnlem.f: |- ( ph -> F e. X_ i e. X ( ( A ` i ) (,) ( B ` i ) ) )
  assume ioorrnopnlem.h: |- H = ran ( i e. X |-> if ( ( ( B ` i ) - ( F ` i ) ) <_ ( ( F ` i ) - ( A ` i ) ) , ( ( B ` i ) - ( F ` i ) ) , ( ( F ` i ) - ( A ` i ) ) ) )
  assume ioorrnopnlem.e: |- E = inf ( H , RR , < )
  assume ioorrnopnlem.v: |- V = ( F ( ball ` D ) E )
  assume ioorrnopnlem.d: |- D = ( f e. ( RR ^m X ) , g e. ( RR ^m X ) |-> ( sqrt ` sum_ k e. X ( ( ( f ` k ) - ( g ` k ) ) ^ 2 ) ) )

  disjoint A g
  disjoint A v
  disjoint B g
  disjoint B v
  disjoint D g
  disjoint D i
  disjoint g i
  disjoint E g
  disjoint E i
  disjoint F g
  disjoint F i
  disjoint F v
  disjoint i v
  disjoint V v
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint X i
  disjoint X v
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint i ph
  disjoint k x
  assert |- ( ph -> E. v e. ( TopOpen ` ( RR^ ` X ) ) ( F e. v /\ v C_ X_ i e. X ( ( A ` i ) (,) ( B ` i ) ) ) )

  proof
    wph
    cV
    cX
    crrx
    cfv
    #
    ctopn
    cfv
    #
    wcel
    #
    cF
    cV
    wcel
    #
    cV
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @4
    cB
    cfv
    #
    cioo
    co
    #
    cixp
    #
    wss
    #
    wa
    #
    cF
    vv
    cv
    #
    wcel
    #
    @11
    @8
    wss
    #
    wa
    #
    vv
    @1
    wrex
    wph
    @2
    cF
    cE
    cD
    cbl
    cfv
    co
    #
    cD
    cmopn
    cfv
    #
    wcel
    #
    wph
    cD
    cr
    cX
    cmap
    co
    #
    cxmt
    cfv
    wcel
    #
    cF
    @18
    wcel
    #
    cE
    cxr
    wcel
    #
    @17
    wph
    cD
    vf
    vg
    vk
    cX
    ioorrnopnlem.x
    ioorrnopnlem.d
    rrndsxmet
    #
    wph
    @8
    @18
    cF
    wph
    vi
    cX
    @7
    cr
    cvv
    wph
    vi
    nfv
    #
    cr
    cvv
    wcel
    wph
    reex
    a1i
    @7
    cr
    wss
    #
    wph
    @4
    cX
    wcel
    #
    wa
    #
    @5
    @6
    ioossre
    #
    a1i
    #
    ixpssmapc
    ioorrnopnlem.f
    sseldd
    #
    wph
    cE
    crp
    wcel
    #
    @21
    wph
    cE
    cH
    cr
    clt
    cinf
    #
    crp
    ioorrnopnlem.e
    wph
    cH
    crp
    @31
    wph
    cH
    vi
    cX
    @6
    @4
    cF
    cfv
    #
    cmin
    co
    #
    @32
    @5
    cmin
    co
    #
    cle
    wbr
    #
    @33
    @34
    cif
    #
    cmpt
    #
    crn
    #
    crp
    cH
    @38
    wceq
    wph
    ioorrnopnlem.h
    a1i
    #
    wph
    @36
    crp
    wcel
    #
    vi
    cX
    wral
    @38
    crp
    wss
    wph
    @40
    vi
    cX
    @26
    @35
    @33
    @34
    crp
    @26
    @33
    @26
    @6
    @32
    wph
    cX
    cr
    @4
    cB
    ioorrnopnlem.b
    ffvelrnda
    #
    @26
    @7
    cr
    @32
    @27
    @26
    cF
    @8
    wcel
    #
    @25
    @32
    @7
    wcel
    #
    wph
    @42
    @25
    ioorrnopnlem.f
    adantr
    wph
    @25
    simpr
    #
    vi
    cX
    @7
    cF
    fvixp2
    syl2anc
    #
    sseldi
    #
    resubcld
    #
    @26
    @32
    @6
    clt
    wbr
    #
    cc0
    @33
    clt
    wbr
    @26
    @5
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @43
    @48
    @26
    @5
    wph
    cX
    cr
    @4
    cA
    ioorrnopnlem.a
    ffvelrnda
    #
    rexrd
    #
    @26
    @6
    @41
    rexrd
    #
    @45
    @5
    @6
    @32
    iooltub
    syl3anc
    @26
    @32
    @6
    @46
    @41
    posdifd
    mpbid
    elrpd
    @26
    @34
    @26
    @32
    @5
    @46
    @51
    resubcld
    #
    @26
    @5
    @32
    clt
    wbr
    #
    cc0
    @34
    clt
    wbr
    @26
    @49
    @50
    @43
    @55
    @52
    @53
    @45
    @5
    @6
    @32
    ioogtlb
    syl3anc
    @26
    @5
    @32
    @51
    @46
    posdifd
    mpbid
    elrpd
    ifcld
    #
    ralrimiva
    vi
    cX
    @36
    crp
    @37
    @37
    eqid
    #
    rnmptss
    syl
    eqsstrd
    #
    wph
    cr
    clt
    wor
    #
    cH
    cfn
    wcel
    #
    cH
    c0
    wne
    #
    cH
    cr
    wss
    #
    @31
    cH
    wcel
    @59
    wph
    ltso
    a1i
    wph
    cH
    @38
    cfn
    ioorrnopnlem.h
    wph
    cX
    cfn
    wcel
    #
    @38
    cfn
    wcel
    ioorrnopnlem.x
    vi
    @37
    cX
    @36
    @57
    rnmptfi
    syl
    syl5eqel
    #
    wph
    cH
    @38
    c0
    @39
    wph
    vi
    cX
    @36
    @37
    cvv
    @23
    @26
    @36
    crp
    @56
    elexd
    #
    @57
    ioorrnopnlem.n
    rnmptn0
    eqnetrd
    #
    wph
    cH
    crp
    cr
    @58
    crp
    cr
    wss
    wph
    rpssre
    a1i
    sstrd
    #
    cr
    cH
    clt
    fiinfcl
    syl13anc
    sseldd
    syl5eqel
    #
    cE
    rpxr
    syl
    #
    cD
    cF
    cE
    @16
    @18
    @16
    eqid
    blopn
    syl3anc
    wph
    cV
    @15
    @1
    @16
    cV
    @15
    wceq
    wph
    ioorrnopnlem.v
    a1i
    #
    wph
    @1
    vf
    vg
    @18
    @18
    cX
    vk
    cv
    #
    vf
    cv
    cfv
    @71
    vg
    cv
    #
    cfv
    cmin
    co
    c2
    cexp
    co
    vk
    csu
    csqrt
    cfv
    cmpt2
    #
    cmopn
    cfv
    @16
    wph
    vf
    vg
    vk
    cX
    ioorrnopnlem.x
    rrxtopnfi
    wph
    @73
    cD
    cmopn
    @73
    cD
    wceq
    wph
    cD
    @73
    ioorrnopnlem.d
    eqcomi
    a1i
    #
    fveq2d
    eqtrd
    eleq12d
    mpbird
    wph
    @3
    @9
    wph
    cF
    @15
    cV
    wph
    cD
    @18
    cpsmet
    cfv
    wcel
    #
    @20
    @30
    cF
    @15
    wcel
    wph
    @19
    @75
    @22
    cD
    @18
    xmetpsmet
    syl
    #
    @29
    @68
    cD
    cF
    cE
    @18
    blcntrps
    syl3anc
    wph
    cV
    @15
    @70
    eqcomd
    eleqtrd
    wph
    cV
    @15
    @8
    @70
    wph
    vg
    @8
    cD
    cF
    cE
    @18
    wph
    vg
    nfv
    @76
    @29
    @69
    wph
    @72
    @18
    wcel
    #
    cF
    @72
    cD
    co
    #
    cE
    clt
    wbr
    #
    w3a
    #
    @72
    cX
    wfn
    #
    @4
    @72
    cfv
    #
    @7
    wcel
    #
    vi
    cX
    wral
    #
    wa
    @72
    @8
    wcel
    @80
    @81
    @84
    @77
    wph
    @81
    @79
    @72
    cr
    cX
    elmapfn
    3ad2ant2
    @80
    @83
    vi
    cX
    @80
    @25
    wa
    #
    @5
    @6
    @82
    wph
    @77
    @25
    @49
    @79
    @52
    3ad2antl1
    wph
    @77
    @25
    @50
    @79
    @53
    3ad2antl1
    @85
    @77
    @25
    @82
    cr
    wcel
    #
    wph
    @77
    @79
    @25
    simpl2
    @80
    @25
    simpr
    @77
    @25
    wa
    cX
    cr
    @4
    @72
    @77
    cX
    cr
    @72
    wf
    #
    @25
    @72
    cr
    cX
    elmapi
    #
    adantr
    @77
    @25
    simpr
    ffvelrnd
    #
    syl2anc
    #
    @85
    @5
    @32
    cE
    cmin
    co
    #
    @82
    wph
    @77
    @25
    @5
    cr
    wcel
    @79
    @51
    3ad2antl1
    wph
    @77
    @25
    @91
    cr
    wcel
    @79
    @26
    @32
    cE
    @46
    wph
    cE
    cr
    wcel
    #
    @25
    wph
    crp
    cr
    cE
    rpssre
    @68
    sseldi
    adantr
    #
    resubcld
    3ad2antl1
    @90
    wph
    @77
    @25
    @5
    @91
    cle
    wbr
    @79
    @26
    cE
    @32
    @5
    @93
    @46
    @51
    @26
    cE
    @36
    @34
    @93
    @26
    crp
    cr
    @36
    rpssre
    @56
    sseldi
    #
    @54
    @26
    cE
    cH
    cxr
    clt
    cinf
    #
    @36
    cle
    wph
    cE
    @95
    wceq
    @25
    wph
    cE
    @31
    @95
    cE
    @31
    wceq
    wph
    ioorrnopnlem.e
    a1i
    wph
    @95
    @31
    wph
    @62
    @60
    @61
    @95
    @31
    wceq
    @67
    @64
    @66
    cH
    infxrrefi
    syl3anc
    eqcomd
    eqtrd
    adantr
    @26
    cH
    cxr
    wss
    #
    @36
    cH
    wcel
    @95
    @36
    cle
    wbr
    wph
    @96
    @25
    wph
    cH
    cr
    cxr
    @67
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    adantr
    @26
    @36
    @38
    cH
    @26
    @25
    @36
    cvv
    wcel
    @36
    @38
    wcel
    @44
    @65
    vi
    cX
    @36
    @37
    cvv
    @57
    elrnmpt1
    syl2anc
    ioorrnopnlem.h
    syl6eleqr
    cH
    @36
    infxrlb
    syl2anc
    eqbrtrd
    #
    @26
    @33
    cr
    wcel
    #
    @34
    cr
    wcel
    #
    @36
    @34
    cle
    wbr
    @47
    @54
    @33
    @34
    min2
    syl2anc
    letrd
    lesubd
    3ad2antl1
    @85
    @32
    @82
    cmin
    co
    #
    cE
    clt
    wbr
    #
    @91
    @82
    clt
    wbr
    #
    @85
    @100
    @78
    cE
    wph
    @77
    @25
    @100
    cr
    wcel
    @79
    wph
    @77
    wa
    #
    @25
    wa
    #
    @32
    @82
    wph
    @25
    @32
    cr
    wcel
    #
    @77
    @46
    adantlr
    #
    @77
    @25
    @86
    wph
    @89
    adantll
    #
    resubcld
    #
    3adantl3
    wph
    @77
    @25
    @78
    cr
    wcel
    #
    @79
    @104
    cD
    @18
    cme
    cfv
    wcel
    #
    @20
    @77
    @109
    wph
    @110
    @77
    @25
    wph
    cD
    vf
    vg
    vk
    cX
    ioorrnopnlem.x
    ioorrnopnlem.d
    rrndsmet
    ad2antrr
    wph
    @20
    @77
    @25
    @29
    ad2antrr
    wph
    @77
    @25
    simplr
    #
    cF
    @72
    cD
    @18
    metcl
    syl3anc
    #
    3adantl3
    #
    wph
    @77
    @25
    @92
    @79
    wph
    @25
    @92
    @77
    @93
    adantlr
    #
    3adantl3
    #
    wph
    @77
    @25
    @100
    @78
    cle
    wbr
    @79
    @104
    @100
    @100
    cabs
    cfv
    #
    @78
    @108
    @104
    @100
    @104
    @100
    @108
    recnd
    abscld
    #
    @112
    @104
    @100
    @108
    leabsd
    @104
    @116
    cF
    @72
    @0
    cds
    cfv
    #
    co
    #
    @78
    cle
    @104
    @118
    cF
    @72
    @4
    cX
    wph
    @63
    @77
    @25
    ioorrnopnlem.x
    ad2antrr
    wph
    cX
    cr
    cF
    wf
    @77
    @25
    wph
    cX
    vi
    cX
    @7
    ciun
    #
    cr
    cF
    wph
    @42
    cX
    @120
    cF
    wf
    ioorrnopnlem.f
    vi
    cX
    @7
    cF
    ixpf
    syl
    wph
    @24
    vi
    cX
    wral
    @120
    cr
    wss
    wph
    @24
    vi
    cX
    @28
    ralrimiva
    vi
    cX
    @7
    cr
    iunss
    sylibr
    fssd
    ad2antrr
    @104
    @77
    @87
    @111
    @88
    syl
    @103
    @25
    simpr
    @118
    eqid
    rrnprjdstle
    wph
    @119
    @78
    wceq
    @77
    @25
    wph
    @118
    cD
    cF
    @72
    wph
    @118
    @73
    cD
    wph
    @63
    @118
    @73
    wceq
    ioorrnopnlem.x
    @18
    vf
    vg
    vk
    @0
    cX
    @0
    eqid
    @18
    eqid
    rrxdsfi
    syl
    @74
    eqtrd
    oveqd
    ad2antrr
    breqtrd
    #
    letrd
    3adantl3
    wph
    @77
    @79
    @25
    simpl3
    #
    lelttrd
    wph
    @77
    @25
    @101
    @102
    wb
    #
    @79
    @104
    @105
    @86
    @92
    @123
    @106
    @107
    @114
    @32
    @82
    cE
    ltsub23
    syl3anc
    3adantl3
    mpbid
    lelttrd
    @85
    @82
    @32
    cE
    caddc
    co
    #
    @6
    @90
    wph
    @77
    @25
    @124
    cr
    wcel
    @79
    @26
    @32
    cE
    @46
    @93
    readdcld
    3ad2antl1
    wph
    @77
    @25
    @6
    cr
    wcel
    @79
    @41
    3ad2antl1
    @85
    @82
    @32
    cmin
    co
    #
    cE
    clt
    wbr
    @82
    @124
    clt
    wbr
    @85
    @125
    @78
    cE
    wph
    @77
    @25
    @125
    cr
    wcel
    @79
    @104
    @82
    @32
    @107
    @106
    resubcld
    #
    3adantl3
    @113
    @115
    wph
    @77
    @25
    @125
    @78
    cle
    wbr
    @79
    @104
    @125
    @116
    @78
    @126
    @117
    @112
    @104
    @125
    @125
    cabs
    cfv
    @116
    cle
    @104
    @125
    @126
    leabsd
    @104
    @82
    @32
    @104
    @82
    @107
    recnd
    @104
    @32
    @106
    recnd
    abssubd
    breqtrd
    @121
    letrd
    3adantl3
    @122
    lelttrd
    @85
    @82
    @32
    cE
    @90
    wph
    @77
    @25
    @105
    @79
    @106
    3adantl3
    @115
    ltsubadd2d
    mpbid
    wph
    @77
    @25
    @124
    @6
    cle
    wbr
    #
    @79
    @26
    @127
    cE
    @33
    cle
    wbr
    @26
    cE
    @36
    @33
    @93
    @94
    @47
    @97
    @26
    @98
    @99
    @36
    @33
    cle
    wbr
    @47
    @54
    @33
    @34
    min1
    syl2anc
    letrd
    @26
    @32
    cE
    @6
    @46
    @93
    @41
    leaddsub2d
    mpbird
    3ad2antl1
    ltletrd
    eliood
    ralrimiva
    jca
    vi
    cX
    @7
    @72
    vg
    vex
    elixp
    sylibr
    ballss3
    eqsstrd
    jca
    @14
    @10
    vv
    cV
    @1
    @11
    cV
    wceq
    @12
    @3
    @13
    @9
    @11
    cV
    cF
    eleq2
    @11
    cV
    @8
    sseq1
    anbi12d
    rspcev
    syl2anc
end
