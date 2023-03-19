include "wacn.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wral.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wex.mm"
include "wf.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "elpw2g.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "ralbidv.mm"
include "biimpar.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "acni.mm"
include "syldan.mm"
include "nffvmpt1.mm"
include "nfel2.mm"
include "nfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "cvv.mm"
include "simplr.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "ssexd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "ex.mm"
include "adantrd.mm"
include "ralimdva.mm"
include "imp.mm"
include "ralbi.mm"
include "syl.mm"
include "biimpa.mm"
include "wi.mm"
include "ssel.mm"
include "adantr.mm"
include "ral2imi.mm"
include "sylc.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "fmptd.mm"
include "acnrcl.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "jca.mm"
include "feq1.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem acni2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let wph: wff ph
  let wps: wff ps
  let cC: class C

  disjoint g x
  disjoint A g
  disjoint A x
  disjoint B g
  disjoint X g
  disjoint X x
  disjoint B f
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g y
  disjoint g z
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint g ph
  disjoint ps y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint X f
  disjoint X h
  disjoint X y
  assert |- ( ( X e. AC_ A /\ A. x e. A ( B C_ X /\ B =/= (/) ) ) -> E. g ( g : A --> X /\ A. x e. A ( g ` x ) e. B ) )

  proof
    cX
    cA
    wacn
    #
    wcel
    #
    cB
    cX
    wss
    #
    cB
    c0
    wne
    #
    wa
    #
    vx
    cA
    wral
    #
    wa
    #
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    @7
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    vf
    wex
    #
    cA
    cX
    vg
    cv
    #
    wf
    #
    vx
    cv
    #
    @15
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
    vg
    wex
    #
    @1
    @5
    cA
    cX
    cpw
    #
    c0
    csn
    cdif
    #
    @10
    wf
    #
    @14
    @6
    cB
    @24
    wcel
    #
    vx
    cA
    wral
    #
    @25
    @1
    @27
    @5
    @1
    @26
    @4
    vx
    cA
    @26
    cB
    @23
    wcel
    #
    @3
    wa
    @1
    @4
    cB
    @23
    c0
    eldifsn
    @1
    @28
    @2
    @3
    cB
    cX
    @0
    elpw2g
    anbi1d
    syl5bb
    ralbidv
    biimpar
    vx
    cA
    @24
    cB
    @10
    @10
    eqid
    #
    fmpt
    sylib
    vy
    cA
    vf
    @10
    cX
    acni
    syldan
    @6
    @13
    @22
    vf
    @13
    @17
    @8
    cfv
    #
    @17
    @10
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    @6
    @22
    @12
    @32
    vy
    vx
    cA
    vx
    @9
    @11
    vx
    cA
    cB
    @7
    nffvmpt1
    nfel2
    @32
    vy
    nfv
    @7
    @17
    wceq
    @9
    @30
    @11
    @31
    @7
    @17
    @8
    fveq2
    #
    @7
    @17
    @10
    fveq2
    eleq12d
    cbvral
    @6
    @33
    @22
    @6
    @33
    wa
    #
    vy
    cA
    @9
    cmpt
    #
    cvv
    wcel
    #
    cA
    cX
    @36
    wf
    #
    @17
    @36
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
    @22
    @35
    @38
    cA
    cvv
    wcel
    #
    @1
    @37
    @35
    vy
    cA
    @9
    cX
    @36
    @35
    @30
    cX
    wcel
    #
    vx
    cA
    wral
    #
    @7
    cA
    wcel
    @9
    cX
    wcel
    #
    @35
    @5
    @30
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @45
    @1
    @5
    @33
    simplr
    @6
    @33
    @48
    @6
    @32
    @47
    wb
    #
    vx
    cA
    wral
    #
    @33
    @48
    wb
    @1
    @5
    @50
    @1
    @4
    @49
    vx
    cA
    @1
    @17
    cA
    wcel
    #
    wa
    #
    @2
    @49
    @3
    @52
    @2
    @49
    @52
    @2
    wa
    #
    @31
    cB
    @30
    @53
    @51
    cB
    cvv
    wcel
    @31
    cB
    wceq
    @1
    @51
    @2
    simplr
    @53
    cB
    cX
    @0
    @1
    @51
    @2
    simpll
    @52
    @2
    simpr
    ssexd
    vx
    cA
    cB
    cvv
    @10
    @29
    fvmpt2
    syl2anc
    eleq2d
    ex
    adantrd
    ralimdva
    imp
    @32
    @47
    vx
    cA
    ralbi
    syl
    biimpa
    #
    @4
    @47
    @44
    vx
    cA
    @2
    @47
    @44
    wi
    @3
    cB
    cX
    @30
    ssel
    adantr
    ral2imi
    sylc
    @44
    @46
    vx
    @7
    cA
    @17
    @7
    wceq
    @30
    @9
    cX
    @17
    @7
    @8
    fveq2
    eleq1d
    rspccva
    sylan
    @36
    eqid
    #
    fmptd
    #
    @35
    @1
    @43
    @1
    @5
    @33
    simpll
    #
    cA
    cX
    acnrcl
    syl
    @57
    cA
    cX
    @36
    cvv
    @0
    fex2
    syl3anc
    @35
    @38
    @41
    @56
    @35
    @48
    @41
    @54
    @40
    @47
    vx
    cA
    @51
    @39
    @30
    cB
    vy
    @17
    @9
    @30
    cA
    @36
    @34
    @55
    @17
    @8
    fvex
    fvmpt
    eleq1d
    ralbiia
    sylibr
    jca
    @21
    @42
    vg
    @36
    cvv
    @15
    @36
    wceq
    #
    @16
    @38
    @20
    @41
    cA
    cX
    @15
    @36
    feq1
    @58
    @19
    @40
    vx
    cA
    @58
    @18
    @39
    cB
    @17
    @15
    @36
    fveq1
    eleq1d
    ralbidv
    anbi12d
    spcegv
    sylc
    ex
    syl5bi
    exlimdv
    mpd
end
