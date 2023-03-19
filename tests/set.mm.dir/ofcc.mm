include "csn.mm"
include "cxp.mm"
include "cofc.mm"
include "co.mm"
include "cmpt.mm"
include "wcel.mm"
include "wfn.mm"
include "fnconstg.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "ofcfval.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"

theorem ofcc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume ofcc.1: |- ( ph -> A e. V )
  assume ofcc.2: |- ( ph -> B e. W )
  assume ofcc.3: |- ( ph -> C e. X )


  assert |- ( ph -> ( ( A X. { B } ) oFC R C ) = ( A X. { ( B R C ) } ) )

  proof
    wph
    cA
    cB
    csn
    cxp
    #
    cC
    cR
    cofc
    co
    vx
    cA
    cB
    cC
    cR
    co
    #
    cmpt
    cA
    @1
    csn
    cxp
    wph
    vx
    cA
    cB
    cC
    cR
    @0
    cV
    cX
    wph
    cB
    cW
    wcel
    #
    @0
    cA
    wfn
    ofcc.2
    cA
    cB
    cW
    fnconstg
    syl
    ofcc.1
    ofcc.3
    wph
    @2
    vx
    cv
    #
    cA
    wcel
    @3
    @0
    cfv
    cB
    wceq
    ofcc.2
    cA
    cB
    @3
    cW
    fvconst2g
    sylan
    ofcfval
    vx
    cA
    @1
    fconstmpt
    syl6eqr
end
