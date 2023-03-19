include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "ciun.mm"
include "cres.mm"
include "iunin1.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "df-res.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtr4ri.mm"

theorem resiun1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- ( U_ x e. A B |` C ) = U_ x e. A ( B |` C )

  proof
    vx
    cA
    cB
    cC
    cvv
    cxp
    #
    cin
    #
    ciun
    vx
    cA
    cB
    ciun
    #
    @0
    cin
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
    vx
    cA
    @0
    cB
    iunin1
    vx
    cA
    @3
    @1
    @3
    @1
    wceq
    vx
    cv
    cA
    wcel
    cB
    cC
    df-res
    a1i
    iuneq2i
    @2
    cC
    df-res
    3eqtr4ri
end
