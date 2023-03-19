include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "ciun.mm"
include "cres.mm"
include "iunin2.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "df-res.mm"
include "incom.mm"
include "eqtri.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtr4ri.mm"

theorem resiun1OLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- ( U_ x e. A B |` C ) = U_ x e. A ( B |` C )

  proof
    vx
    cA
    cC
    cvv
    cxp
    #
    cB
    cin
    #
    ciun
    @0
    vx
    cA
    cB
    ciun
    #
    cin
    #
    vx
    cA
    cB
    cC
    cres
    #
    ciun
    @2
    cC
    cres
    #
    vx
    cA
    @0
    cB
    iunin2
    vx
    cA
    @4
    @1
    @4
    @1
    wceq
    vx
    cv
    cA
    wcel
    @4
    cB
    @0
    cin
    @1
    cB
    cC
    df-res
    cB
    @0
    incom
    eqtri
    a1i
    iuneq2i
    @5
    @2
    @0
    cin
    @3
    @2
    cC
    df-res
    @2
    @0
    incom
    eqtri
    3eqtr4ri
end
