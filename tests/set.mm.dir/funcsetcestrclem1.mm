include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "adantr.mm"
include "opeq2.mm"
include "sneqd.mm"
include "adantl.mm"
include "simpr.mm"
include "snex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem funcsetcestrclem1
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

  disjoint C x
  disjoint X x
  disjoint ph x
  assert |- ( ( ph /\ X e. C ) -> ( F ` X ) = { <. ( Base ` ndx ) , X >. } )

  proof
    wph
    cX
    cC
    wcel
    #
    wa
    #
    vx
    cX
    cnx
    cbs
    cfv
    #
    vx
    cv
    #
    cop
    #
    csn
    #
    @2
    cX
    cop
    #
    csn
    #
    cC
    cF
    cvv
    wph
    cF
    vx
    cC
    @5
    cmpt
    wceq
    @0
    funcsetcestrc.f
    adantr
    @3
    cX
    wceq
    #
    @5
    @7
    wceq
    @1
    @8
    @4
    @6
    @3
    cX
    @2
    opeq2
    sneqd
    adantl
    wph
    @0
    simpr
    @7
    cvv
    wcel
    @1
    @6
    snex
    a1i
    fvmptd
end
