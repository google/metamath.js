include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cbs.mm"
include "funcringcsetcALTV2lem1.mm"
include "ringcbasbas.mm"
include "eqeltrd.mm"

theorem funcringcsetcALTV2lem2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cX: class X
  let vk: setvar k
  assume funcringcsetcALTV2.r: |- R = ( RingCat ` U )
  assume funcringcsetcALTV2.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV2.b: |- B = ( Base ` R )
  assume funcringcsetcALTV2.c: |- C = ( Base ` S )
  assume funcringcsetcALTV2.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV2.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint k x
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
    cR
    cS
    cU
    cF
    cX
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem1
    wph
    cB
    cR
    cX
    cU
    funcringcsetcALTV2.r
    funcringcsetcALTV2.b
    funcringcsetcALTV2.u
    ringcbasbas
    eqeltrd
end
