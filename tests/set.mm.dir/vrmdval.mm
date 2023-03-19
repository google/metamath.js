include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cs1.mm"
include "cword.mm"
include "cmpt.mm"
include "wceq.mm"
include "vrmdfval.mm"
include "adantr.mm"
include "s1eq.mm"
include "adantl.mm"
include "simpr.mm"
include "s1cl.mm"
include "fvmptd.mm"

theorem vrmdval
  let cA: class A
  let cU: class U
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vi: setvar i
  assume vrmdfval.u: |- U = ( varFMnd ` I )


  assert |- ( ( I e. V /\ A e. I ) -> ( U ` A ) = <" A "> )

  proof
    cI
    cV
    wcel
    #
    cA
    cI
    wcel
    #
    wa
    #
    vj
    cA
    vj
    cv
    #
    cs1
    #
    cA
    cs1
    #
    cI
    cU
    cI
    cword
    #
    @0
    cU
    vj
    cI
    @4
    cmpt
    wceq
    @1
    cU
    vj
    cI
    cV
    vrmdfval.u
    vrmdfval
    adantr
    @3
    cA
    wceq
    @4
    @5
    wceq
    @2
    @3
    cA
    s1eq
    adantl
    @0
    @1
    simpr
    @1
    @5
    @6
    wcel
    @0
    cA
    cI
    s1cl
    adantl
    fvmptd
end
