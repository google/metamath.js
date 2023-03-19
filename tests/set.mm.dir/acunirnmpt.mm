include "cuni.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simpr.mm"
include "simplll.mm"
include "simplr.mm"
include "syl2anc.mm"
include "eqnetrd.mm"
include "cmpt.mm"
include "crn.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "bitri.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "wi.mm"
include "mptexg.mm"
include "rnexg.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "raleq.mm"
include "id.mm"
include "unieq.mm"
include "feq23d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "ac5b.mm"
include "vtoclg.mm"
include "syl.mm"
include "mpd.mm"
include "adantr.mm"
include "simpllr.mm"
include "eleqtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "anim2d.mm"
include "eximdv.mm"

theorem acunirnmpt
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vj: setvar j
  let cV: class V
  let vc: setvar c
  assume acunirnmpt.0: |- ( ph -> A e. V )
  assume acunirnmpt.1: |- ( ( ph /\ j e. A ) -> B =/= (/) )
  assume acunirnmpt.2: |- C = ran ( j e. A |-> B )

  disjoint A j
  disjoint f j
  disjoint f y
  disjoint C f
  disjoint j y
  disjoint C j
  disjoint C y
  disjoint f ph
  disjoint j ph
  disjoint ph y
  disjoint c f
  disjoint c j
  disjoint c y
  disjoint C c
  assert |- ( ph -> E. f ( f : C --> U. C /\ A. y e. C E. j e. A ( f ` y ) e. B ) )

  proof
    wph
    cC
    cC
    cuni
    #
    vf
    cv
    #
    wf
    #
    vy
    cv
    #
    @1
    cfv
    #
    @3
    wcel
    #
    vy
    cC
    wral
    #
    wa
    #
    vf
    wex
    #
    @2
    @4
    cB
    wcel
    #
    vj
    cA
    wrex
    #
    vy
    cC
    wral
    #
    wa
    #
    vf
    wex
    wph
    @3
    c0
    wne
    #
    vy
    cC
    wral
    #
    @8
    wph
    @13
    vy
    cC
    wph
    @3
    cC
    wcel
    #
    wa
    #
    @3
    cB
    wceq
    #
    @13
    vj
    cA
    @16
    vj
    cv
    cA
    wcel
    #
    wa
    #
    @17
    wa
    #
    @3
    cB
    c0
    @19
    @17
    simpr
    @20
    wph
    @18
    cB
    c0
    wne
    wph
    @15
    @18
    @17
    simplll
    @16
    @18
    @17
    simplr
    acunirnmpt.1
    syl2anc
    eqnetrd
    @15
    @17
    vj
    cA
    wrex
    #
    wph
    @15
    @21
    @15
    @3
    vj
    cA
    cB
    cmpt
    #
    crn
    #
    wcel
    #
    @21
    cC
    @23
    @3
    acunirnmpt.2
    eleq2i
    @3
    cvv
    wcel
    @24
    @21
    wb
    vy
    vex
    vj
    cA
    cB
    @3
    @22
    cvv
    @22
    eqid
    elrnmpt
    ax-mp
    bitri
    biimpi
    adantl
    #
    r19.29a
    ralrimiva
    wph
    cC
    cvv
    wcel
    @14
    @8
    wi
    #
    wph
    cC
    @23
    cvv
    acunirnmpt.2
    wph
    cA
    cV
    wcel
    @22
    cvv
    wcel
    @23
    cvv
    wcel
    acunirnmpt.0
    vj
    cA
    cB
    cV
    mptexg
    @22
    cvv
    rnexg
    3syl
    syl5eqel
    @13
    vy
    vc
    cv
    #
    wral
    #
    @27
    @27
    cuni
    #
    @1
    wf
    #
    @5
    vy
    @27
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    @26
    vc
    cC
    cvv
    @27
    cC
    wceq
    #
    @28
    @14
    @33
    @8
    @13
    vy
    @27
    cC
    raleq
    @34
    @32
    @7
    vf
    @34
    @30
    @2
    @31
    @6
    @34
    @27
    @29
    cC
    @0
    @1
    @34
    id
    @27
    cC
    unieq
    feq23d
    @5
    vy
    @27
    cC
    raleq
    anbi12d
    exbidv
    imbi12d
    vy
    @27
    vf
    vc
    vex
    ac5b
    vtoclg
    syl
    mpd
    wph
    @7
    @12
    vf
    wph
    @6
    @11
    @2
    wph
    @5
    @10
    vy
    cC
    @16
    @5
    @10
    @16
    @5
    wa
    #
    @21
    @10
    @16
    @21
    @5
    @25
    adantr
    @35
    @17
    @9
    vj
    cA
    @35
    @18
    wa
    #
    @17
    @9
    @36
    @17
    wa
    @4
    @3
    cB
    @16
    @5
    @18
    @17
    simpllr
    @36
    @17
    simpr
    eleqtrd
    ex
    reximdva
    mpd
    ex
    ralimdva
    anim2d
    eximdv
    mpd
end
