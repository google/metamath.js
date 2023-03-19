include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "wceq.mm"
include "cab.mm"
include "wcel.mm"
include "df-sn.mm"
include "equcom.mm"
include "abbii.mm"
include "eqtri.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "wrex.mm"
include "iunab.mm"
include "risset.mm"
include "abid2.mm"
include "3eqtr2i.mm"

theorem iunid
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- U_ x e. A { x } = A

  proof
    vx
    cA
    vx
    cv
    #
    csn
    #
    ciun
    vx
    cA
    @0
    vy
    cv
    #
    wceq
    #
    vy
    cab
    #
    ciun
    #
    cA
    vx
    cA
    @1
    @4
    @1
    @4
    wceq
    @0
    cA
    wcel
    @1
    @2
    @0
    wceq
    #
    vy
    cab
    @4
    vy
    @0
    df-sn
    @6
    @3
    vy
    vy
    vx
    equcom
    abbii
    eqtri
    a1i
    iuneq2i
    @5
    @3
    vx
    cA
    wrex
    #
    vy
    cab
    @2
    cA
    wcel
    #
    vy
    cab
    cA
    @3
    vx
    vy
    cA
    iunab
    @8
    @7
    vy
    vx
    @2
    cA
    risset
    abbii
    vy
    cA
    abid2
    3eqtr2i
    eqtri
end
