include "ciun.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "csb.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wf1.mm"
include "c2nd.mm"
include "wceq.mm"
include "wex.mm"
include "nfiu1.mm"
include "nfcsb1v.mm"
include "eqid.mm"
include "csbeq1a.mm"
include "acunirnmpt2f.mm"
include "cop.mm"
include "cmpt.mm"
include "wi.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcv.mm"
include "nff.mm"
include "nfel.mm"
include "nfral.mm"
include "wrex.mm"
include "simplr.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "simpllr.mm"
include "ffvelrnd.mm"
include "fvex.mm"
include "snid.mm"
include "a1i.mm"
include "simprd.mm"
include "simpr.mm"
include "rsp.mm"
include "sylc.mm"
include "jca.mm"
include "opelxp.mm"
include "sylibr.mm"
include "sneq.mm"
include "csbeq1.mm"
include "xpeq12d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eliun.mm"
include "nfxp.mm"
include "cbvrexf.mm"
include "bitri.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29af2.mm"
include "ex.mm"
include "ralrimi.mm"
include "vex.mm"
include "opth.mm"
include "simprbi.mm"
include "rgen2w.mm"
include "fveq2.mm"
include "id.mm"
include "opeq12d.mm"
include "f1mpt.mm"
include "cvv.mm"
include "opex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "syl.mm"
include "fveq2d.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "ralrimiva.mm"
include "cbviunf.mm"
include "iunexg.mm"
include "syl5eqel.mm"
include "mptexg.mm"
include "f1eq1.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbid.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "3syl.mm"
include "adantr.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem aciunf1lem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vy: setvar y
  let vg: setvar g
  assume acunirnmpt.0: |- ( ph -> A e. V )
  assume acunirnmpt.1: |- ( ( ph /\ j e. A ) -> B =/= (/) )
  assume aciunf1lem.a: |- F/_ j A
  assume aciunf1lem.1: |- ( ( ph /\ j e. A ) -> B e. W )

  disjoint f j
  disjoint f x
  disjoint A f
  disjoint A x
  disjoint B f
  disjoint B x
  disjoint j x
  disjoint j ph
  disjoint ph x
  disjoint W j
  disjoint f k
  disjoint f y
  disjoint j k
  disjoint j y
  disjoint k y
  disjoint f g
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint k x
  disjoint A k
  disjoint x y
  disjoint A y
  disjoint B g
  disjoint B k
  disjoint B y
  disjoint g j
  disjoint g ph
  disjoint k ph
  assert |- ( ph -> E. f ( f : U_ j e. A B -1-1-> U_ j e. A ( { j } X. B ) /\ A. x e. U_ j e. A B ( 2nd ` ( f ` x ) ) = x ) )

  proof
    wph
    vj
    cA
    cB
    ciun
    #
    cA
    vg
    cv
    #
    wf
    #
    vx
    cv
    #
    vj
    @3
    @1
    cfv
    #
    cB
    csb
    #
    wcel
    #
    vx
    @0
    wral
    #
    wa
    #
    @0
    vj
    cA
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    vf
    cv
    #
    wf1
    #
    @3
    @13
    cfv
    #
    c2nd
    cfv
    #
    @3
    wceq
    #
    vx
    @0
    wral
    #
    wa
    #
    vf
    wex
    #
    vg
    wph
    vx
    cA
    cB
    @0
    @5
    vg
    vj
    cV
    cW
    acunirnmpt.0
    acunirnmpt.1
    aciunf1lem.a
    vj
    cA
    cB
    nfiu1
    #
    vj
    @4
    cB
    nfcsb1v
    #
    @0
    eqid
    vj
    @4
    cB
    csbeq1a
    aciunf1lem.1
    acunirnmpt2f
    wph
    @8
    wa
    #
    @0
    @12
    vx
    @0
    @4
    @3
    cop
    #
    cmpt
    #
    wf1
    #
    @3
    @25
    cfv
    #
    c2nd
    cfv
    #
    @3
    wceq
    #
    vx
    @0
    wral
    #
    wa
    #
    @20
    @23
    @26
    @30
    @23
    @24
    @12
    wcel
    #
    vx
    @0
    wral
    #
    @24
    vy
    cv
    #
    @1
    cfv
    #
    @34
    cop
    #
    wceq
    #
    @3
    @34
    wceq
    #
    wi
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    wa
    @26
    @23
    @33
    @40
    @23
    @32
    vx
    @0
    wph
    @8
    vx
    wph
    vx
    nfv
    @2
    @7
    vx
    @2
    vx
    nfv
    @6
    vx
    @0
    nfra1
    nfan
    nfan
    #
    @23
    @3
    @0
    wcel
    #
    @32
    @23
    @42
    wa
    #
    @3
    cB
    wcel
    #
    @32
    vj
    cA
    @23
    @42
    vj
    wph
    @8
    vj
    wph
    vj
    nfv
    #
    @2
    @7
    vj
    vj
    @0
    cA
    @1
    vj
    @1
    nfcv
    @21
    aciunf1lem.a
    nff
    @6
    vj
    vx
    @0
    @21
    vj
    @3
    @5
    vj
    @3
    nfcv
    #
    @22
    nfel
    nfral
    nfan
    nfan
    vj
    @3
    @0
    @46
    @21
    nfel
    nfan
    vj
    @24
    @12
    vj
    @24
    nfcv
    #
    vj
    cA
    @11
    nfiu1
    nfel
    @43
    @9
    cA
    wcel
    #
    wa
    @44
    wa
    #
    @24
    vk
    cv
    #
    csn
    #
    vj
    @50
    cB
    csb
    #
    cxp
    #
    wcel
    #
    vk
    cA
    wrex
    #
    @32
    @49
    @4
    cA
    wcel
    @24
    @4
    csn
    #
    @5
    cxp
    #
    wcel
    #
    @55
    @49
    @0
    cA
    @3
    @1
    @43
    @2
    @48
    @44
    @43
    @2
    @7
    wph
    @8
    @42
    simplr
    #
    simpld
    ad2antrr
    @23
    @42
    @48
    @44
    simpllr
    ffvelrnd
    @49
    @4
    @56
    wcel
    #
    @6
    wa
    @58
    @49
    @60
    @6
    @60
    @49
    @4
    @3
    @1
    fvex
    #
    snid
    a1i
    @43
    @6
    @48
    @44
    @43
    @7
    @42
    @6
    @43
    @2
    @7
    @59
    simprd
    @23
    @42
    simpr
    #
    @6
    vx
    @0
    rsp
    sylc
    ad2antrr
    jca
    @4
    @3
    @56
    @5
    opelxp
    sylibr
    @54
    @58
    vk
    @4
    cA
    @50
    @4
    wceq
    #
    @53
    @57
    @24
    @63
    @51
    @56
    @52
    @5
    @50
    @4
    sneq
    vj
    @50
    @4
    cB
    csbeq1
    xpeq12d
    eleq2d
    rspcev
    syl2anc
    @32
    @24
    @11
    wcel
    #
    vj
    cA
    wrex
    @55
    vj
    @24
    cA
    @11
    eliun
    @64
    @54
    vj
    vk
    cA
    aciunf1lem.a
    vk
    cA
    nfcv
    #
    @64
    vk
    nfv
    vj
    @24
    @53
    @47
    vj
    @51
    @52
    vj
    @51
    nfcv
    vj
    @50
    cB
    nfcsb1v
    #
    nfxp
    nfel
    @9
    @50
    wceq
    #
    @11
    @53
    @24
    @67
    @10
    @51
    cB
    @52
    @9
    @50
    sneq
    vj
    @50
    cB
    csbeq1a
    #
    xpeq12d
    eleq2d
    cbvrexf
    bitri
    sylibr
    @42
    @44
    vj
    cA
    wrex
    #
    @23
    @42
    @69
    vj
    @3
    cA
    cB
    eliun
    biimpi
    adantl
    r19.29af2
    ex
    ralrimi
    @40
    @23
    @39
    vx
    vy
    @0
    @0
    @37
    @4
    @35
    wceq
    @38
    @4
    @3
    @35
    @34
    @61
    vx
    vex
    #
    opth
    simprbi
    rgen2w
    a1i
    jca
    vx
    vy
    @0
    @12
    @24
    @36
    @25
    @25
    eqid
    #
    @38
    @4
    @35
    @3
    @34
    @3
    @34
    @1
    fveq2
    @38
    id
    opeq12d
    f1mpt
    sylibr
    @23
    @29
    vx
    @0
    @41
    @23
    @42
    @29
    @43
    @28
    @24
    c2nd
    cfv
    @3
    @43
    @27
    @24
    c2nd
    @43
    @42
    @27
    @24
    wceq
    #
    @62
    @42
    @24
    cvv
    wcel
    @72
    @4
    @3
    opex
    vx
    @0
    @24
    cvv
    @25
    @71
    fvmpt2
    mpan2
    syl
    fveq2d
    @4
    @3
    @61
    @70
    op2nd
    syl6eq
    ex
    ralrimi
    jca
    wph
    @31
    @20
    wi
    #
    @8
    wph
    @0
    cvv
    wcel
    #
    @25
    cvv
    wcel
    @73
    wph
    cA
    cV
    wcel
    #
    @52
    cW
    wcel
    #
    vk
    cA
    wral
    #
    @74
    acunirnmpt.0
    wph
    @76
    vk
    cA
    wph
    @48
    wa
    #
    cB
    cW
    wcel
    #
    wi
    wph
    @50
    cA
    wcel
    #
    wa
    #
    @76
    wi
    vj
    vk
    @81
    @76
    vj
    wph
    @80
    vj
    @45
    vj
    @50
    cA
    vj
    @50
    nfcv
    aciunf1lem.a
    nfel
    nfan
    vj
    @52
    cW
    @66
    vj
    cW
    nfcv
    nfel
    nfim
    @67
    @78
    @81
    @79
    @76
    @67
    @48
    @80
    wph
    @9
    @50
    cA
    eleq1
    anbi2d
    @67
    cB
    @52
    cW
    @68
    eleq1d
    imbi12d
    aciunf1lem.1
    chvar
    ralrimiva
    @75
    @77
    wa
    @0
    vk
    cA
    @52
    ciun
    cvv
    vj
    vk
    cA
    cB
    @52
    aciunf1lem.a
    @65
    vk
    cB
    nfcv
    @66
    @68
    cbviunf
    vk
    cA
    @52
    cV
    cW
    iunexg
    syl5eqel
    syl2anc
    vx
    @0
    @24
    cvv
    mptexg
    @19
    @31
    vf
    @25
    cvv
    @13
    @25
    wceq
    #
    @14
    @26
    @18
    @30
    @0
    @12
    @13
    @25
    f1eq1
    @82
    @17
    @29
    vx
    @0
    vx
    @13
    @25
    vx
    @13
    nfcv
    vx
    @0
    @24
    nfmpt1
    nfeq
    @82
    @16
    @28
    @3
    @82
    @15
    @27
    c2nd
    @3
    @13
    @25
    fveq1
    fveq2d
    eqeq1d
    ralbid
    anbi12d
    spcegv
    3syl
    adantr
    mpd
    exlimddv
end
