include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cfn.mm"
include "mptfi.mm"
include "syl.mm"
include "rnfi.mm"
include "fnchoice.mm"
include "simpl.mm"
include "simprl.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rspa.mm"
include "adantll.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "w3a.mm"
include "simp3.mm"
include "3adant3.mm"
include "eqnetrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "adantr.mm"
include "mpd.mm"
include "adantlr.mm"
include "id.mm"
include "imp.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "rsp.mm"
include "adantrl.mm"
include "ccom.mm"
include "a1i.mm"
include "mptexd.mm"
include "coexg.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "simpr.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "ssid.mm"
include "fnco.mm"
include "syl3anc.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nffn.mm"
include "nfral.mm"
include "nf3an.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "dmmptd.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "fvmpt2.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "3ad2antl1.mm"
include "elrnmpt1.mm"
include "simpl3.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "rspcva.mm"
include "eqeltrd.mm"
include "jca.mm"
include "fneq1.mm"
include "nfco.mm"
include "nfeq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "ralbid.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "exlimdv.mm"

theorem choicefi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cW: class W
  let vg: setvar g
  let vy: setvar y
  assume choicefi.a: |- ( ph -> A e. Fin )
  assume choicefi.b: |- ( ( ph /\ x e. A ) -> B e. W )
  assume choicefi.n: |- ( ( ph /\ x e. A ) -> B =/= (/) )

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint B f
  disjoint ph x
  disjoint A g
  disjoint f g
  disjoint g x
  disjoint A y
  disjoint g y
  disjoint x y
  disjoint B g
  disjoint B y
  disjoint g ph
  disjoint ph y
  assert |- ( ph -> E. f ( f Fn A /\ A. x e. A ( f ` x ) e. B ) )

  proof
    wph
    vg
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    wfn
    #
    vy
    cv
    #
    c0
    wne
    #
    @4
    @0
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vy
    @2
    wral
    #
    wa
    #
    vg
    wex
    #
    vf
    cv
    #
    cA
    wfn
    #
    vx
    cv
    #
    @12
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    wph
    @2
    cfn
    wcel
    #
    @11
    wph
    @1
    cfn
    wcel
    #
    @20
    wph
    cA
    cfn
    wcel
    @21
    choicefi.a
    vx
    cA
    cB
    mptfi
    syl
    @1
    rnfi
    syl
    vy
    @2
    vg
    fnchoice
    syl
    wph
    @10
    @19
    vg
    wph
    @10
    @19
    wph
    @10
    wa
    wph
    @3
    @7
    vy
    @2
    wral
    #
    @19
    wph
    @10
    simpl
    wph
    @3
    @9
    simprl
    wph
    @9
    @22
    @3
    wph
    @9
    wa
    #
    @7
    vy
    @2
    wph
    @9
    vy
    wph
    vy
    nfv
    @8
    vy
    @2
    nfra1
    nfan
    #
    @23
    @22
    @4
    @2
    wcel
    #
    @7
    wi
    @23
    @7
    vy
    @2
    @24
    @23
    @25
    @7
    @23
    @25
    wa
    @8
    @5
    @7
    @9
    @25
    @8
    wph
    @8
    vy
    @2
    rspa
    adantll
    wph
    @25
    @5
    @9
    wph
    @25
    wa
    @4
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @5
    @25
    @27
    wph
    @25
    @27
    @4
    cvv
    wcel
    @25
    @27
    wb
    vy
    vex
    vx
    cA
    cB
    @4
    @1
    cvv
    @1
    eqid
    #
    elrnmpt
    ax-mp
    biimpi
    adantl
    wph
    @27
    @5
    wi
    @25
    wph
    @26
    @5
    vx
    cA
    wph
    @14
    cA
    wcel
    #
    @26
    @5
    wph
    @29
    @26
    w3a
    @4
    cB
    c0
    wph
    @29
    @26
    simp3
    wph
    @29
    cB
    c0
    wne
    @26
    choicefi.n
    3adant3
    eqnetrd
    3exp
    rexlimdv
    adantr
    mpd
    adantlr
    @8
    @5
    @7
    @8
    id
    imp
    syl2anc
    ex
    ralrimi
    @7
    vy
    @2
    rsp
    syl
    ralrimi
    adantrl
    wph
    @3
    @22
    w3a
    #
    @0
    @1
    ccom
    #
    cvv
    wcel
    #
    @31
    cA
    wfn
    #
    @14
    @31
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @19
    wph
    @3
    @32
    @22
    wph
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    @32
    @38
    wph
    vg
    vex
    a1i
    wph
    vx
    cA
    cB
    cfn
    choicefi.a
    mptexd
    @0
    @1
    cvv
    cvv
    coexg
    syl2anc
    3ad2ant1
    @30
    @33
    @36
    wph
    @3
    @33
    @22
    wph
    @3
    wa
    #
    @3
    @1
    cA
    wfn
    #
    @2
    @2
    wss
    #
    @33
    wph
    @3
    simpr
    wph
    @40
    @3
    wph
    cB
    cW
    wcel
    #
    vx
    cA
    wral
    @40
    wph
    @42
    vx
    cA
    choicefi.b
    ralrimiva
    vx
    cA
    cB
    @1
    cW
    @28
    fnmpt
    syl
    adantr
    @41
    @39
    @2
    ssid
    a1i
    @2
    cA
    @0
    @1
    fnco
    syl3anc
    3adant3
    @30
    @35
    vx
    cA
    wph
    @3
    @22
    vx
    wph
    vx
    nfv
    vx
    @2
    @0
    vx
    @0
    nfcv
    #
    vx
    @1
    vx
    cA
    cB
    nfmpt1
    #
    nfrn
    #
    nffn
    @7
    vx
    vy
    @2
    @45
    @7
    vx
    nfv
    nfral
    nf3an
    @30
    @29
    @35
    @30
    @29
    wa
    #
    @34
    cB
    @0
    cfv
    #
    cB
    wph
    @3
    @29
    @34
    @47
    wceq
    @22
    wph
    @29
    wa
    #
    @34
    @14
    @1
    cfv
    #
    @0
    cfv
    #
    @47
    @48
    @1
    wfun
    #
    @14
    @1
    cdm
    #
    wcel
    @34
    @50
    wceq
    @51
    @48
    vx
    cA
    cB
    funmpt
    a1i
    @48
    @14
    cA
    @52
    wph
    @29
    simpr
    #
    wph
    cA
    @52
    wceq
    @29
    wph
    @52
    cA
    wph
    vx
    @1
    cA
    cB
    cW
    @28
    choicefi.b
    dmmptd
    eqcomd
    adantr
    eleqtrd
    @14
    @0
    @1
    fvco
    syl2anc
    @48
    @49
    cB
    @0
    @48
    @29
    @42
    @49
    cB
    wceq
    @53
    choicefi.b
    vx
    cA
    cB
    cW
    @1
    @28
    fvmpt2
    syl2anc
    fveq2d
    eqtrd
    3ad2antl1
    @46
    cB
    @2
    wcel
    #
    @22
    @47
    cB
    wcel
    #
    wph
    @3
    @29
    @54
    @22
    @48
    @29
    @42
    @54
    @53
    choicefi.b
    vx
    cA
    cB
    @1
    cW
    @28
    elrnmpt1
    syl2anc
    3ad2antl1
    wph
    @3
    @22
    @29
    simpl3
    @7
    @55
    vy
    cB
    @2
    @26
    @6
    @47
    @4
    cB
    @4
    cB
    @0
    fveq2
    @26
    id
    eleq12d
    rspcva
    syl2anc
    eqeltrd
    ex
    ralrimi
    jca
    @18
    @37
    vf
    @31
    cvv
    @12
    @31
    wceq
    #
    @13
    @33
    @17
    @36
    cA
    @12
    @31
    fneq1
    @56
    @16
    @35
    vx
    cA
    vx
    @12
    @31
    vx
    @12
    nfcv
    vx
    @0
    @1
    @43
    @44
    nfco
    nfeq
    @56
    @15
    @34
    cB
    @14
    @12
    @31
    fveq1
    eleq1d
    ralbid
    anbi12d
    spcegv
    sylc
    syl3anc
    ex
    exlimdv
    mpd
end
