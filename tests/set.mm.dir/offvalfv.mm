include "cv.mm"
include "cfv.mm"
include "crn.mm"
include "wfn.mm"
include "wcel.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "cmpt.mm"
include "wceq.mm"
include "dffn5.mm"
include "sylib.mm"
include "offval2.mm"

theorem offvalfv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume offvalfv.a: |- ( ph -> A e. V )
  assume offvalfv.f: |- ( ph -> F Fn A )
  assume offvalfv.g: |- ( ph -> G Fn A )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint R x
  disjoint k x
  assert |- ( ph -> ( F oF R G ) = ( x e. A |-> ( ( F ` x ) R ( G ` x ) ) ) )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    cR
    cF
    cG
    cV
    cF
    crn
    #
    cG
    crn
    #
    offvalfv.a
    wph
    cF
    cA
    wfn
    #
    @0
    cA
    wcel
    #
    @1
    @3
    wcel
    offvalfv.f
    cA
    @0
    cF
    fnfvelrn
    sylan
    wph
    cG
    cA
    wfn
    #
    @6
    @2
    @4
    wcel
    offvalfv.g
    cA
    @0
    cG
    fnfvelrn
    sylan
    wph
    @5
    cF
    vx
    cA
    @1
    cmpt
    wceq
    offvalfv.f
    vx
    cA
    cF
    dffn5
    sylib
    wph
    @7
    cG
    vx
    cA
    @2
    cmpt
    wceq
    offvalfv.g
    vx
    cA
    cG
    dffn5
    sylib
    offval2
end
