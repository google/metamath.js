include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "csn.mm"
include "funcsetcestrclem1.mm"
include "setc1strwun.mm"
include "eqeltrd.mm"

theorem funcsetcestrclem2
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cX: class X
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )

  disjoint C x
  disjoint X x
  disjoint ph x
  assert |- ( ( ph /\ X e. C ) -> ( F ` X ) e. U )

  proof
    wph
    cX
    cC
    wcel
    wa
    cX
    cF
    cfv
    cnx
    cbs
    cfv
    cX
    cop
    csn
    cU
    wph
    vx
    cC
    cS
    cU
    cF
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    wph
    cC
    cS
    cU
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.u
    funcsetcestrc.o
    setc1strwun
    eqeltrd
end
