include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "elex.mm"
include "cpointsN.mm"
include "cfv.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rexeqdv.mm"
include "abbidv.mm"
include "df-pointsN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "abrexex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem pointsetN
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let vp: setvar p
  let va: setvar a
  let vk: setvar k
  assume pointset.a: |- A = ( Atoms ` K )
  assume pointset.p: |- P = ( Points ` K )

  disjoint a p
  disjoint A a
  disjoint A p
  disjoint K p
  disjoint a k
  disjoint k p
  disjoint A k
  disjoint K k
  assert |- ( K e. B -> P = { p | E. a e. A p = { a } } )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cP
    vp
    cv
    va
    cv
    csn
    #
    wceq
    #
    va
    cA
    wrex
    #
    vp
    cab
    #
    wceq
    cK
    cB
    elex
    @0
    cP
    cK
    cpointsN
    cfv
    @4
    pointset.p
    vk
    cK
    @2
    va
    vk
    cv
    #
    catm
    cfv
    #
    wrex
    #
    vp
    cab
    @4
    cvv
    cpointsN
    @5
    cK
    wceq
    #
    @7
    @3
    vp
    @8
    @2
    va
    @6
    cA
    @8
    @6
    cK
    catm
    cfv
    #
    cA
    @5
    cK
    catm
    fveq2
    pointset.a
    syl6eqr
    rexeqdv
    abbidv
    vk
    vp
    va
    df-pointsN
    va
    vp
    cA
    @1
    cA
    @9
    cvv
    pointset.a
    cK
    catm
    fvex
    eqeltri
    abrexex
    fvmpt
    syl5eq
    syl
end
