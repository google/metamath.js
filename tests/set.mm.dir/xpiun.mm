include "weq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "ciun.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "xpsnopab.mm"
include "eqcomi.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "iunxpconst.mm"
include "eqtr2i.mm"

theorem xpiun
  let vx: setvar x
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vk: setvar k

  disjoint B x
  disjoint C a
  disjoint C b
  disjoint C x
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint k x
  assert |- ( B X. C ) = U_ x e. B { <. a , b >. | ( a = x /\ b e. C ) }

  proof
    vx
    cB
    va
    vx
    weq
    vb
    cv
    cC
    wcel
    wa
    va
    vb
    copab
    #
    ciun
    vx
    cB
    vx
    cv
    #
    csn
    cC
    cxp
    #
    ciun
    cB
    cC
    cxp
    vx
    cB
    @0
    @2
    @0
    @2
    wceq
    @1
    cB
    wcel
    @2
    @0
    cC
    @1
    va
    vb
    xpsnopab
    eqcomi
    a1i
    iuneq2i
    vx
    cB
    cC
    iunxpconst
    eqtr2i
end
