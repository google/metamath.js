include "cofc.mm"
include "co.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-ofc.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "dmeqd.mm"
include "fveq1d.mm"
include "simprr.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "wfn.mm"
include "wcel.mm"
include "fnex.mm"
include "syl2anc.mm"
include "elex.mm"
include "syl.mm"
include "fndm.mm"
include "eqeltrd.mm"
include "mptexg.mm"
include "ovmpt2d.mm"
include "eleq2d.mm"
include "pm5.32i.mm"
include "sylbi.mm"
include "oveq1d.mm"
include "mpteq12dva.mm"
include "eqtrd.mm"

theorem ofcfval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vf: setvar f
  assume ofcfval.1: |- ( ph -> F Fn A )
  assume ofcfval.2: |- ( ph -> A e. V )
  assume ofcfval.3: |- ( ph -> C e. W )
  assume ofcfval.6: |- ( ( ph /\ x e. A ) -> ( F ` x ) = B )

  disjoint C x
  disjoint F x
  disjoint R x
  disjoint ph x
  disjoint c f
  disjoint c x
  disjoint C c
  disjoint f x
  disjoint C f
  disjoint F c
  disjoint F f
  disjoint R c
  disjoint R f
  disjoint c ph
  disjoint f ph
  assert |- ( ph -> ( F oFC R C ) = ( x e. A |-> ( B R C ) ) )

  proof
    wph
    cF
    cC
    cR
    cofc
    #
    co
    vx
    cF
    cdm
    #
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cR
    co
    #
    cmpt
    #
    vx
    cA
    cB
    cC
    cR
    co
    #
    cmpt
    wph
    vf
    vc
    cF
    cC
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    #
    @2
    @7
    cfv
    #
    vc
    cv
    #
    cR
    co
    #
    cmpt
    #
    @5
    @0
    cvv
    @0
    vf
    vc
    cvv
    cvv
    @12
    cmpt2
    wceq
    wph
    vx
    cR
    vf
    vc
    df-ofc
    a1i
    wph
    @7
    cF
    wceq
    #
    @10
    cC
    wceq
    #
    wa
    wa
    #
    vx
    @8
    @11
    @1
    @4
    @15
    @7
    cF
    wph
    @13
    @14
    simprl
    #
    dmeqd
    @15
    @9
    @3
    @10
    cC
    cR
    @15
    @2
    @7
    cF
    @16
    fveq1d
    wph
    @13
    @14
    simprr
    oveq12d
    mpteq12dv
    wph
    cF
    cA
    wfn
    #
    cA
    cV
    wcel
    cF
    cvv
    wcel
    ofcfval.1
    ofcfval.2
    cA
    cV
    cF
    fnex
    syl2anc
    wph
    cC
    cW
    wcel
    cC
    cvv
    wcel
    ofcfval.3
    cC
    cW
    elex
    syl
    wph
    @1
    cV
    wcel
    @5
    cvv
    wcel
    wph
    @1
    cA
    cV
    wph
    @17
    @1
    cA
    wceq
    ofcfval.1
    cA
    cF
    fndm
    syl
    #
    ofcfval.2
    eqeltrd
    vx
    @1
    @4
    cV
    mptexg
    syl
    ovmpt2d
    wph
    vx
    @1
    @4
    cA
    @6
    @18
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    cB
    cC
    cR
    @20
    wph
    @2
    cA
    wcel
    #
    wa
    @3
    cB
    wceq
    wph
    @19
    @21
    wph
    @1
    cA
    @2
    @18
    eleq2d
    pm5.32i
    ofcfval.6
    sylbi
    oveq1d
    mpteq12dva
    eqtrd
end
