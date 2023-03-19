include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wreu.mm"
include "risset.mm"
include "wrmo.mm"
include "wmo.mm"
include "moeq.mm"
include "mormo.mm"
include "ax-mp.mm"
include "reu5.mm"
include "mpbiran2.mm"
include "bitr4i.mm"

theorem reueq
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( B e. A <-> E! x e. A x = B )

  proof
    cB
    cA
    wcel
    vx
    cv
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    vx
    cA
    wreu
    #
    vx
    cB
    cA
    risset
    @2
    @1
    @0
    vx
    cA
    wrmo
    #
    @0
    vx
    wmo
    @3
    vx
    cB
    moeq
    @0
    vx
    cA
    mormo
    ax-mp
    @0
    vx
    cA
    reu5
    mpbiran2
    bitr4i
end
