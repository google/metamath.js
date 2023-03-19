include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "simplr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylib.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "wi.mm"
include "simpllr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "ex.mm"
include "reximdai.mm"
include "mpd.mm"
include "cuni.mm"
include "ciun.mm"
include "ralrimiva.mm"
include "dfiun3g.mm"
include "syl.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eluni2.mm"
include "r19.29a.mm"
include "csb.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "rnexg.mm"
include "uniexg.mm"
include "4syl.mm"
include "eqeltrd.mm"
include "id.mm"
include "raleqdv.mm"
include "feq2d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "cfv.mm"
include "ac6sf2.mm"
include "vtoclg.mm"

theorem acunirnmpt2f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vj: setvar j
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vy: setvar y
  let vk: setvar k
  assume acunirnmpt.0: |- ( ph -> A e. V )
  assume acunirnmpt.1: |- ( ( ph /\ j e. A ) -> B =/= (/) )
  assume aciunf1lem.a: |- F/_ j A
  assume acunirnmpt2f.c: |- F/_ j C
  assume acunirnmpt2f.d: |- F/_ j D
  assume acunirnmpt2f.2: |- C = U_ j e. A B
  assume acunirnmpt2f.3: |- ( j = ( f ` x ) -> B = D )
  assume acunirnmpt2f.4: |- ( ( ph /\ j e. A ) -> B e. W )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint B f
  disjoint C f
  disjoint C x
  disjoint f j
  disjoint f ph
  disjoint j x
  disjoint j ph
  disjoint ph x
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint c k
  disjoint A c
  disjoint f y
  disjoint f k
  disjoint x y
  disjoint k x
  disjoint k y
  disjoint A y
  disjoint A k
  disjoint B c
  disjoint B k
  disjoint B y
  disjoint C c
  disjoint C y
  disjoint D c
  disjoint j k
  disjoint j y
  disjoint k ph
  disjoint ph y
  disjoint c j
  assert |- ( ph -> E. f ( f : C --> A /\ A. x e. C x e. D ) )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    vj
    cA
    wrex
    #
    vx
    cC
    wral
    #
    cC
    cA
    vf
    cv
    #
    wf
    #
    @0
    cD
    wcel
    #
    vx
    cC
    wral
    #
    wa
    #
    vf
    wex
    #
    wph
    @2
    vx
    cC
    wph
    @0
    cC
    wcel
    #
    wa
    #
    @0
    vy
    cv
    #
    wcel
    #
    @2
    vy
    vj
    cA
    cB
    cmpt
    #
    crn
    #
    @11
    @12
    @15
    wcel
    #
    wa
    #
    @13
    wa
    #
    @12
    cB
    wceq
    #
    vj
    cA
    wrex
    #
    @2
    @18
    @16
    @20
    @11
    @16
    @13
    simplr
    @12
    cvv
    wcel
    @16
    @20
    wb
    vy
    vex
    vj
    cA
    cB
    @12
    @14
    cvv
    @14
    eqid
    elrnmpt
    ax-mp
    sylib
    @18
    @19
    @1
    vj
    cA
    @17
    @13
    vj
    @11
    @16
    vj
    wph
    @10
    vj
    wph
    vj
    nfv
    vj
    vx
    cC
    acunirnmpt2f.c
    nfcri
    nfan
    vj
    @12
    @15
    vj
    @12
    nfcv
    vj
    @14
    vj
    cA
    cB
    nfmpt1
    nfrn
    nfel
    nfan
    @13
    vj
    nfv
    nfan
    @18
    vj
    cv
    #
    cA
    wcel
    #
    @19
    @1
    wi
    @18
    @22
    wa
    #
    @19
    @1
    @23
    @19
    wa
    @0
    @12
    cB
    @17
    @13
    @22
    @19
    simpllr
    @23
    @19
    simpr
    eleqtrd
    ex
    ex
    reximdai
    mpd
    @11
    @0
    @15
    cuni
    #
    wcel
    #
    @13
    vy
    @15
    wrex
    wph
    @10
    @25
    wph
    cC
    @24
    @0
    wph
    cC
    vj
    cA
    cB
    ciun
    #
    @24
    acunirnmpt2f.2
    wph
    cB
    cW
    wcel
    #
    vj
    cA
    wral
    @26
    @24
    wceq
    wph
    @27
    vj
    cA
    acunirnmpt2f.4
    ralrimiva
    vj
    cA
    cB
    cW
    dfiun3g
    syl
    syl5eq
    #
    eleq2d
    biimpa
    vy
    @0
    @15
    eluni2
    sylib
    r19.29a
    ralrimiva
    wph
    cC
    cvv
    wcel
    @3
    @9
    wi
    #
    wph
    cC
    @24
    cvv
    @28
    wph
    cA
    cV
    wcel
    #
    @14
    cvv
    wcel
    @15
    cvv
    wcel
    @24
    cvv
    wcel
    acunirnmpt.0
    @30
    @14
    vk
    cA
    vj
    vk
    cv
    #
    cB
    csb
    #
    cmpt
    cvv
    vj
    vk
    cA
    cB
    @32
    aciunf1lem.a
    vk
    cA
    nfcv
    vk
    cB
    nfcv
    vj
    @31
    cB
    nfcsb1v
    vj
    @31
    cB
    csbeq1a
    cbvmptf
    vk
    cA
    @32
    cV
    mptexg
    syl5eqel
    @14
    cvv
    rnexg
    @15
    cvv
    uniexg
    4syl
    eqeltrd
    @2
    vx
    vc
    cv
    #
    wral
    #
    @33
    cA
    @4
    wf
    #
    @6
    vx
    @33
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    @29
    vc
    cC
    cvv
    @33
    cC
    wceq
    #
    @34
    @3
    @38
    @9
    @39
    @2
    vx
    @33
    cC
    @39
    id
    #
    raleqdv
    @39
    @37
    @8
    vf
    @39
    @35
    @5
    @36
    @7
    @39
    @33
    cC
    cA
    @4
    @40
    feq2d
    @39
    @6
    vx
    @33
    cC
    @40
    raleqdv
    anbi12d
    exbidv
    imbi12d
    @1
    @6
    vx
    vj
    @33
    cA
    vf
    aciunf1lem.a
    vj
    vx
    cD
    acunirnmpt2f.d
    nfcri
    vc
    vex
    @21
    @0
    @4
    cfv
    wceq
    cB
    cD
    @0
    acunirnmpt2f.3
    eleq2d
    ac6sf2
    vtoclg
    syl
    mpd
end
