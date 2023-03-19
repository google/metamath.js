include "c0.mm"
include "wceq.mm"
include "csu.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "a1d.mm"
include "necon4bd.mm"
include "caddc.mm"
include "cmpt.mm"
include "ccom.mm"
include "cseq.mm"
include "sumfc.mm"
include "fveq2.mm"
include "simprl.mm"
include "simprr.mm"
include "cc.mm"
include "wss.mm"
include "ad2antrr.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "sseldd.mm"
include "f1of.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "fsum.mm"
include "syl5eqr.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fco.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "seqcl.mm"
include "eqeltrd.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fsumcl2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  assume fsumcllem.1: |- ( ph -> S C_ CC )
  assume fsumcllem.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume fsumcllem.3: |- ( ph -> A e. Fin )
  assume fsumcllem.4: |- ( ( ph /\ k e. A ) -> B e. S )
  assume fsumcl2lem.5: |- ( ph -> A =/= (/) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint f ph
  disjoint m ph
  disjoint S f
  assert |- ( ph -> sum_ k e. A B e. S )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    vk
    csu
    #
    cS
    wcel
    #
    cA
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @3
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    wph
    @2
    cA
    c0
    wph
    cA
    c0
    wne
    @2
    wn
    fsumcl2lem.5
    a1d
    necon4bd
    wph
    @4
    @8
    @2
    wph
    @4
    wa
    @7
    @2
    vf
    wph
    @4
    @7
    @2
    wph
    @4
    @7
    wa
    #
    wa
    #
    @1
    @3
    caddc
    vk
    cA
    cB
    cmpt
    #
    @6
    ccom
    #
    c1
    cseq
    cfv
    #
    cS
    @11
    @1
    cA
    vm
    cv
    #
    @12
    cfv
    #
    vm
    csu
    @14
    cA
    cB
    vm
    vk
    sumfc
    @11
    cA
    @16
    vx
    cv
    #
    @6
    cfv
    #
    @12
    cfv
    #
    vm
    vx
    @6
    @13
    @3
    @15
    @18
    @12
    fveq2
    wph
    @4
    @7
    simprl
    #
    wph
    @4
    @7
    simprr
    #
    @11
    @15
    cA
    wcel
    #
    wa
    cS
    cc
    @16
    wph
    cS
    cc
    wss
    @10
    @22
    fsumcllem.1
    ad2antrr
    @11
    cA
    cS
    @15
    @12
    wph
    cA
    cS
    @12
    wf
    #
    @10
    wph
    vk
    cA
    cB
    cS
    @12
    fsumcllem.4
    @12
    eqid
    fmptd
    adantr
    #
    ffvelrnda
    sseldd
    @11
    @5
    cA
    @6
    wf
    #
    @17
    @5
    wcel
    @17
    @13
    cfv
    @19
    wceq
    @11
    @7
    @25
    @21
    @5
    cA
    @6
    f1of
    syl
    #
    @5
    cA
    @17
    @12
    @6
    fvco3
    sylan
    fsum
    syl5eqr
    @11
    vx
    vy
    caddc
    cS
    @13
    c1
    @3
    @11
    @3
    cn
    c1
    cuz
    cfv
    @20
    nnuz
    syl6eleq
    @11
    @5
    cS
    @17
    @13
    @11
    @23
    @25
    @5
    cS
    @13
    wf
    @24
    @26
    @5
    cA
    cS
    @12
    @6
    fco
    syl2anc
    ffvelrnda
    wph
    @17
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    @17
    @27
    caddc
    co
    cS
    wcel
    @10
    fsumcllem.2
    adantlr
    seqcl
    eqeltrd
    expr
    exlimdv
    expimpd
    wph
    cA
    cfn
    wcel
    @0
    @9
    wo
    fsumcllem.3
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
