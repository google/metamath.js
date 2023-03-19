include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wfn.mm"
include "fnconstg.mm"
include "syl.mm"
include "inidm.mm"
include "cfv.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "ofval.mm"

theorem ofc1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  assume ofc1.1: |- ( ph -> A e. V )
  assume ofc1.2: |- ( ph -> B e. W )
  assume ofc1.3: |- ( ph -> F Fn A )
  assume ofc1.4: |- ( ( ph /\ X e. A ) -> ( F ` X ) = C )


  assert |- ( ( ph /\ X e. A ) -> ( ( ( A X. { B } ) oF R F ) ` X ) = ( B R C ) )

  proof
    wph
    cA
    cA
    cB
    cC
    cR
    cA
    cA
    cB
    csn
    cxp
    #
    cF
    cV
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
    ofc1.2
    cA
    cB
    cW
    fnconstg
    syl
    ofc1.3
    ofc1.1
    ofc1.1
    cA
    inidm
    wph
    @1
    cX
    cA
    wcel
    cX
    @0
    cfv
    cB
    wceq
    ofc1.2
    cA
    cB
    cX
    cW
    fvconst2g
    sylan
    ofc1.4
    ofval
end
