include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cofc.mm"
include "ccom.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "mpteq1d.mm"
include "cvv.mm"
include "wcel.mm"
include "fex.mm"
include "syl2anc.mm"
include "ofcfval3.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "oveq1.mm"
include "fmptco.mm"
include "3eqtr4d.mm"

theorem ofcfval4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vy: setvar y
  assume ofcfval4.1: |- ( ph -> F : A --> B )
  assume ofcfval4.2: |- ( ph -> A e. V )
  assume ofcfval4.3: |- ( ph -> C e. W )

  disjoint B x
  disjoint C x
  disjoint F x
  disjoint R x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint F y
  disjoint R y
  disjoint ph y
  assert |- ( ph -> ( F oFC R C ) = ( ( x e. B |-> ( x R C ) ) o. F ) )

  proof
    wph
    vy
    cF
    cdm
    #
    vy
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
    vy
    cA
    @3
    cmpt
    cF
    cC
    cR
    cofc
    co
    #
    vx
    cB
    vx
    cv
    #
    cC
    cR
    co
    #
    cmpt
    #
    cF
    ccom
    wph
    vy
    @0
    cA
    @3
    wph
    cA
    cB
    cF
    wf
    #
    @0
    cA
    wceq
    ofcfval4.1
    cA
    cB
    cF
    fdm
    syl
    mpteq1d
    wph
    cF
    cvv
    wcel
    #
    cC
    cW
    wcel
    @5
    @4
    wceq
    wph
    @9
    cA
    cV
    wcel
    @10
    ofcfval4.1
    ofcfval4.2
    cA
    cB
    cV
    cF
    fex
    syl2anc
    ofcfval4.3
    vy
    cC
    cR
    cF
    cvv
    cW
    ofcfval3
    syl2anc
    wph
    vy
    vx
    cA
    cB
    @2
    @7
    @3
    cF
    @8
    wph
    cA
    cB
    @1
    cF
    ofcfval4.1
    ffvelrnda
    wph
    vy
    cA
    cB
    cF
    ofcfval4.1
    feqmptd
    wph
    @8
    eqidd
    @6
    @2
    cC
    cR
    oveq1
    fmptco
    3eqtr4d
end
