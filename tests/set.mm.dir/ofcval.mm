include "wcel.mm"
include "wa.mm"
include "cofc.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqidd.mm"
include "ofcfval.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "eqtrd.mm"

theorem ofcval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vc: setvar c
  let vf: setvar f
  assume ofcfval.1: |- ( ph -> F Fn A )
  assume ofcfval.2: |- ( ph -> A e. V )
  assume ofcfval.3: |- ( ph -> C e. W )
  assume ofcval.6: |- ( ( ph /\ X e. A ) -> ( F ` X ) = B )


  assert |- ( ( ph /\ X e. A ) -> ( ( F oFC R C ) ` X ) = ( B R C ) )

  proof
    wph
    cX
    cA
    wcel
    #
    wa
    #
    cX
    cF
    cC
    cR
    cofc
    co
    #
    cfv
    cX
    cF
    cfv
    #
    cC
    cR
    co
    #
    cB
    cC
    cR
    co
    @1
    vx
    cX
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
    @4
    cA
    @2
    cvv
    wph
    @2
    vx
    cA
    @7
    cmpt
    wceq
    @0
    wph
    vx
    cA
    @6
    cC
    cR
    cF
    cV
    cW
    ofcfval.1
    ofcfval.2
    ofcfval.3
    wph
    @5
    cA
    wcel
    wa
    @6
    eqidd
    ofcfval
    adantr
    @1
    @5
    cX
    wceq
    #
    wa
    #
    @6
    @3
    cC
    cR
    @9
    @5
    cX
    cF
    @1
    @8
    simpr
    fveq2d
    oveq1d
    wph
    @0
    simpr
    @1
    @3
    cC
    cR
    ovexd
    fvmptd
    @1
    @3
    cB
    cC
    cR
    ofcval.6
    oveq1d
    eqtrd
end
