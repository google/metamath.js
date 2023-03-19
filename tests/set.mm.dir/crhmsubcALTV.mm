include "ccrg.mm"
include "cv.mm"
include "crg.mm"
include "wcel.mm"
include "crngring.mm"
include "rgen.mm"
include "srhmsubcALTV.mm"

theorem crhmsubcALTV
  let cC: class C
  let cU: class U
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume crhmsubcALTV.c: |- C = ( U i^i CRing )
  assume crhmsubcALTV.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )

  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint k x
  assert |- ( U e. V -> J e. ( Subcat ` ( RingCatALTV ` U ) ) )

  proof
    cC
    ccrg
    cU
    cJ
    cV
    vs
    vr
    vr
    cv
    #
    crg
    wcel
    vr
    ccrg
    @0
    crngring
    rgen
    crhmsubcALTV.c
    crhmsubcALTV.j
    srhmsubcALTV
end
