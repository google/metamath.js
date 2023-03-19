include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "df-xp.mm"
include "velsn.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem xpsnopab
  let cC: class C
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x

  disjoint C a
  disjoint C b
  disjoint a b
  disjoint X a
  disjoint X b
  disjoint k x
  assert |- ( { X } X. C ) = { <. a , b >. | ( a = X /\ b e. C ) }

  proof
    cX
    csn
    #
    cC
    cxp
    va
    cv
    #
    @0
    wcel
    #
    vb
    cv
    cC
    wcel
    #
    wa
    #
    va
    vb
    copab
    @1
    cX
    wceq
    #
    @3
    wa
    #
    va
    vb
    copab
    va
    vb
    @0
    cC
    df-xp
    @4
    @6
    va
    vb
    @2
    @5
    @3
    va
    cX
    velsn
    anbi1i
    opabbii
    eqtri
end
