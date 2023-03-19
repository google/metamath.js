include "ciun.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wrex.mm"
include "dfss2.mm"
include "df-ral.mm"
include "eliun.mm"
include "ralbii.mm"
include "3bitr2ri.mm"

theorem ssiun3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A. y e. C E. x e. A y e. B <-> C C_ U_ x e. A B )

  proof
    cC
    vx
    cA
    cB
    ciun
    #
    wss
    vy
    cv
    #
    cC
    wcel
    @1
    @0
    wcel
    #
    wi
    vy
    wal
    @2
    vy
    cC
    wral
    @1
    cB
    wcel
    vx
    cA
    wrex
    #
    vy
    cC
    wral
    vy
    cC
    @0
    dfss2
    @2
    vy
    cC
    df-ral
    @2
    @3
    vy
    cC
    vx
    @1
    cA
    cB
    eliun
    ralbii
    3bitr2ri
end
