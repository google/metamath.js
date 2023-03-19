include "ciun.mm"
include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "xpiundir.mm"
include "ineq2i.mm"
include "iunin2.mm"
include "eqtr4i.mm"

theorem resiun2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- ( C |` U_ x e. A B ) = U_ x e. A ( C |` B )

  proof
    cC
    vx
    cA
    cB
    ciun
    #
    cres
    cC
    @0
    cvv
    cxp
    #
    cin
    #
    vx
    cA
    cC
    cB
    cres
    #
    ciun
    #
    cC
    @0
    df-res
    @4
    vx
    cA
    cC
    cB
    cvv
    cxp
    #
    cin
    #
    ciun
    #
    @2
    vx
    cA
    @3
    @6
    @3
    @6
    wceq
    vx
    cv
    cA
    wcel
    cC
    cB
    df-res
    a1i
    iuneq2i
    @2
    cC
    vx
    cA
    @5
    ciun
    #
    cin
    @7
    @1
    @8
    cC
    vx
    cA
    cB
    cvv
    xpiundir
    ineq2i
    vx
    cA
    cC
    @5
    iunin2
    eqtr4i
    eqtr4i
    eqtr4i
end
