include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "adantr.mm"
include "fveq2.mm"
include "adantl.mm"
include "simpr.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem funcestrcsetclem1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cX: class X
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  assert |- ( ( ph /\ X e. B ) -> ( F ` X ) = ( Base ` X ) )

  proof
    wph
    cX
    cB
    wcel
    #
    wa
    #
    vx
    cX
    vx
    cv
    #
    cbs
    cfv
    #
    cX
    cbs
    cfv
    #
    cB
    cF
    cvv
    wph
    cF
    vx
    cB
    @3
    cmpt
    wceq
    @0
    funcestrcsetc.f
    adantr
    @2
    cX
    wceq
    @3
    @4
    wceq
    @1
    @2
    cX
    cbs
    fveq2
    adantl
    wph
    @0
    simpr
    @1
    cX
    cbs
    fvexd
    fvmptd
end
