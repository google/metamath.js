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

theorem ofc2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  assume ofc2.1: |- ( ph -> A e. V )
  assume ofc2.2: |- ( ph -> B e. W )
  assume ofc2.3: |- ( ph -> F Fn A )
  assume ofc2.4: |- ( ( ph /\ X e. A ) -> ( F ` X ) = C )


  assert |- ( ( ph /\ X e. A ) -> ( ( F oF R ( A X. { B } ) ) ` X ) = ( C R B ) )

  proof
    wph
    cA
    cA
    cC
    cB
    cR
    cA
    cF
    cA
    cB
    csn
    cxp
    #
    cV
    cV
    cX
    ofc2.3
    wph
    cB
    cW
    wcel
    #
    @0
    cA
    wfn
    ofc2.2
    cA
    cB
    cW
    fnconstg
    syl
    ofc2.1
    ofc2.1
    cA
    inidm
    ofc2.4
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
    ofc2.2
    cA
    cB
    cX
    cW
    fvconst2g
    sylan
    ofval
end
