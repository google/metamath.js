include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cbs.mm"
include "funcringcsetclem1ALTV.mm"
include "ringcbasbasALTV.mm"
include "eqeltrd.mm"

theorem funcringcsetclem2ALTV
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
  assume funcringcsetcALTV.r: |- R = ( RingCatALTV ` U )
  assume funcringcsetcALTV.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV.b: |- B = ( Base ` R )
  assume funcringcsetcALTV.c: |- C = ( Base ` S )
  assume funcringcsetcALTV.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )

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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem1ALTV
    wph
    cB
    cR
    cX
    cU
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    funcringcsetcALTV.u
    ringcbasbasALTV
    eqeltrd
end
