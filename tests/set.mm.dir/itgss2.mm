include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "citg.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "itgeq2dv.mm"
include "id.mm"
include "cdif.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "itgss.mm"
include "eqtr3d.mm"

theorem itgss2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> S. A C _d x = S. B if ( x e. A , C , 0 ) _d x )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    citg
    vx
    cA
    cC
    citg
    vx
    cB
    @3
    citg
    @0
    vx
    cA
    @3
    cC
    @2
    @3
    cC
    wceq
    @0
    @2
    cC
    cc0
    iftrue
    adantl
    itgeq2dv
    @0
    vx
    cA
    cB
    @3
    @0
    id
    @1
    cB
    cA
    cdif
    wcel
    #
    @3
    cc0
    wceq
    @0
    @4
    @2
    cC
    cc0
    @1
    cB
    cA
    eldifn
    iffalsed
    adantl
    itgss
    eqtr3d
end
