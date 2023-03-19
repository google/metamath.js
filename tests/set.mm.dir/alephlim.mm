include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "char.mm"
include "com.mm"
include "crdg.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "cale.mm"
include "rdglim2a.mm"
include "df-aleph.mm"
include "fveq1i.mm"
include "wceq.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "3eqtr4g.mm"

theorem alephlim
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( ( A e. V /\ Lim A ) -> ( aleph ` A ) = U_ x e. A ( aleph ` x ) )

  proof
    cA
    cV
    wcel
    cA
    wlim
    wa
    cA
    char
    com
    crdg
    #
    cfv
    vx
    cA
    vx
    cv
    #
    @0
    cfv
    #
    ciun
    cA
    cale
    cfv
    vx
    cA
    @1
    cale
    cfv
    #
    ciun
    vx
    com
    cA
    cV
    char
    rdglim2a
    cA
    cale
    @0
    df-aleph
    fveq1i
    vx
    cA
    @3
    @2
    @3
    @2
    wceq
    @1
    cA
    wcel
    @1
    cale
    @0
    df-aleph
    fveq1i
    a1i
    iuneq2i
    3eqtr4g
end
