include "c0.mm"
include "wceq.mm"
include "cprod.mm"
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
include "cmul.mm"
include "cmpt.mm"
include "ccom.mm"
include "cseq.mm"
include "prodfc.mm"
include "fveq2.mm"
include "simprl.mm"
include "simprr.mm"
include "cc.mm"
include "wss.mm"
include "adantr.mm"
include "sseldd.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antll.mm"
include "fvco3.mm"
include "sylan.mm"
include "fprod.mm"
include "syl5eqr.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fco.mm"
include "syl2anc.mm"
include "seqcl.mm"
include "eqeltrd.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "syl.mm"
include "mpjaod.mm"

theorem fprodcl2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  assume fprodcllem.1: |- ( ph -> S C_ CC )
  assume fprodcllem.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume fprodcllem.3: |- ( ph -> A e. Fin )
  assume fprodcllem.4: |- ( ( ph /\ k e. A ) -> B e. S )
  assume fprodcl2lem.5: |- ( ph -> A =/= (/) )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A f
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint f k
  disjoint f m
  disjoint f ph
  disjoint f x
  disjoint f y
  disjoint k m
  disjoint m ph
  disjoint m x
  disjoint S f
  assert |- ( ph -> prod_ k e. A B e. S )

  proof
    wph
    cA
    c0
    wceq
    #
    cA
    cB
    vk
    cprod
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
    fprodcl2lem.5
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
    cmul
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
    cprod
    @14
    cA
    cB
    vm
    vk
    prodfc
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
    wph
    @15
    cA
    wcel
    @16
    cc
    wcel
    @10
    wph
    cA
    cc
    @15
    @12
    wph
    vk
    cA
    cB
    cc
    @12
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    cS
    cc
    cB
    wph
    cS
    cc
    wss
    @21
    fprodcllem.1
    adantr
    fprodcllem.4
    sseldd
    @12
    eqid
    #
    fmptd
    ffvelrnda
    adantlr
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
    @7
    @23
    wph
    @4
    @5
    cA
    @6
    f1of
    ad2antll
    #
    @5
    cA
    @17
    @12
    @6
    fvco3
    sylan
    fprod
    syl5eqr
    @11
    vx
    vy
    cmul
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
    cA
    cS
    @12
    wf
    #
    @23
    @5
    cS
    @13
    wf
    wph
    @25
    @10
    wph
    vk
    cA
    cB
    cS
    @12
    fprodcllem.4
    @22
    fmptd
    adantr
    @24
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
    @26
    cmul
    co
    cS
    wcel
    @10
    fprodcllem.2
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
    fprodcllem.3
    cA
    vf
    fz1f1o
    syl
    mpjaod
end
