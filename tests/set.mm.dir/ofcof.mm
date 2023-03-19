include "cofc.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "ofcfval.mm"
include "fnconstg.mm"
include "inidm.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "offval.mm"
include "eqtr4d.mm"

theorem ofcof
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume ofcof.1: |- ( ph -> F : A --> B )
  assume ofcof.2: |- ( ph -> A e. V )
  assume ofcof.3: |- ( ph -> C e. W )


  assert |- ( ph -> ( F oFC R C ) = ( F oF R ( A X. { C } ) ) )

  proof
    wph
    cF
    cC
    cR
    cofc
    co
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cR
    co
    cmpt
    cF
    cA
    cC
    csn
    cxp
    #
    cR
    cof
    co
    wph
    vx
    cA
    @1
    cC
    cR
    cF
    cV
    cW
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    ofcof.1
    cA
    cB
    cF
    ffn
    syl
    #
    ofcof.2
    ofcof.3
    wph
    @0
    cA
    wcel
    #
    wa
    @1
    eqidd
    #
    ofcfval
    wph
    vx
    cA
    cA
    @1
    cC
    cR
    cA
    cF
    @2
    cV
    cV
    @3
    wph
    cC
    cW
    wcel
    #
    @2
    cA
    wfn
    ofcof.3
    cA
    cC
    cW
    fnconstg
    syl
    ofcof.2
    ofcof.2
    cA
    inidm
    @5
    wph
    @6
    @4
    @0
    @2
    cfv
    cC
    wceq
    ofcof.3
    cA
    cC
    @0
    cW
    fvconst2g
    sylan
    offval
    eqtr4d
end
