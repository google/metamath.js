include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cbs.mm"
include "funcestrcsetclem1.mm"
include "estrcbasbas.mm"
include "eqeltrd.mm"

theorem funcestrcsetclem2
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
  assert |- ( ( ph /\ X e. B ) -> ( F ` X ) e. U )

  proof
    wph
    cX
    cB
    wcel
    wa
    cX
    cF
    cfv
    cX
    cbs
    cfv
    cU
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    wph
    cB
    cE
    cU
    cX
    funcestrcsetc.e
    funcestrcsetc.b
    funcestrcsetc.u
    estrcbasbas
    eqeltrd
end
