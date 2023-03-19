include "wpss.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wex.mm"
include "wn.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "pssdif.mm"
include "n0.mm"
include "sylib.mm"
include "eldif.mm"
include "exbii.mm"

theorem pssnel
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C. B -> E. x ( x e. B /\ -. x e. A ) )

  proof
    cA
    cB
    wpss
    #
    vx
    cv
    #
    cB
    cA
    cdif
    #
    wcel
    #
    vx
    wex
    #
    @1
    cB
    wcel
    @1
    cA
    wcel
    wn
    wa
    #
    vx
    wex
    @0
    @2
    c0
    wne
    @4
    cA
    cB
    pssdif
    vx
    @2
    n0
    sylib
    @3
    @5
    vx
    @1
    cB
    cA
    eldif
    exbii
    sylib
end
