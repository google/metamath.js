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
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfan.mm"
include "wi.mm"
include "simpllr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "ex.mm"
include "reximdai.mm"
include "mpd.mm"
include "cuni.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluni2.mm"
include "adantl.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "mptexg.mm"
include "rnexg.mm"
include "uniexg.mm"
include "4syl.mm"
include "syl5eqel.mm"
include "id.mm"
include "raleqdv.mm"
include "feq2d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "cfv.mm"
include "eleq2d.mm"
include "ac6s.mm"
include "vtoclg.mm"
include "syl.mm"

theorem acunirnmpt2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vj: setvar j
  let cV: class V
  let vc: setvar c
  let vy: setvar y
  assume acunirnmpt.0: |- ( ph -> A e. V )
  assume acunirnmpt.1: |- ( ( ph /\ j e. A ) -> B =/= (/) )
  assume acunirnmpt2.2: |- C = U. ran ( j e. A |-> B )
  assume acunirnmpt2.3: |- ( j = ( f ` x ) -> B = D )

  disjoint f j
  disjoint f x
  disjoint A f
  disjoint j x
  disjoint A j
  disjoint A x
  disjoint B f
  disjoint C f
  disjoint C j
  disjoint C x
  disjoint D j
  disjoint f ph
  disjoint j ph
  disjoint ph x
  disjoint c f
  disjoint c j
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f y
  disjoint j y
  disjoint x y
  disjoint A y
  disjoint B c
  disjoint B y
  disjoint C c
  disjoint C y
  disjoint D c
  disjoint ph y
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
    @11
    vj
    nfv
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
    @10
    @13
    vy
    @15
    wrex
    #
    wph
    @10
    @0
    @15
    cuni
    #
    wcel
    #
    @24
    @10
    @26
    cC
    @25
    @0
    acunirnmpt2.2
    eleq2i
    biimpi
    vy
    @0
    @15
    eluni2
    sylib
    adantl
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
    @25
    cvv
    acunirnmpt2.2
    wph
    cA
    cV
    wcel
    @14
    cvv
    wcel
    @15
    cvv
    wcel
    @25
    cvv
    wcel
    acunirnmpt.0
    vj
    cA
    cB
    cV
    mptexg
    @14
    cvv
    rnexg
    @15
    cvv
    uniexg
    4syl
    syl5eqel
    @2
    vx
    vc
    cv
    #
    wral
    #
    @28
    cA
    @4
    wf
    #
    @6
    vx
    @28
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    @27
    vc
    cC
    cvv
    @28
    cC
    wceq
    #
    @29
    @3
    @33
    @9
    @34
    @2
    vx
    @28
    cC
    @34
    id
    #
    raleqdv
    @34
    @32
    @8
    vf
    @34
    @30
    @5
    @31
    @7
    @34
    @28
    cC
    cA
    @4
    @35
    feq2d
    @34
    @6
    vx
    @28
    cC
    @35
    raleqdv
    anbi12d
    exbidv
    imbi12d
    @1
    @6
    vx
    vj
    @28
    cA
    vf
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
    acunirnmpt2.3
    eleq2d
    ac6s
    vtoclg
    syl
    mpd
end
