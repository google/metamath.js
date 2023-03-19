include "cv.mm"
include "cuni.mm"
include "wcel.mm"
include "wel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wrex.mm"
include "r19.23v.mm"
include "albii.mm"
include "ralcom4.mm"
include "eluni2.mm"
include "imbi1i.mm"
include "3bitr4ri.mm"
include "df-ral.mm"
include "ralbii.mm"
include "3bitr4i.mm"

theorem untuni
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A. x e. U. A -. x e. x <-> A. y e. A A. x e. y -. x e. x )

  proof
    vx
    cv
    #
    cA
    cuni
    #
    wcel
    #
    vx
    vx
    wel
    wn
    #
    wi
    #
    vx
    wal
    #
    vx
    vy
    wel
    #
    @3
    wi
    #
    vx
    wal
    #
    vy
    cA
    wral
    #
    @3
    vx
    @1
    wral
    @3
    vx
    vy
    cv
    #
    wral
    #
    vy
    cA
    wral
    @7
    vy
    cA
    wral
    #
    vx
    wal
    @6
    vy
    cA
    wrex
    #
    @3
    wi
    #
    vx
    wal
    @9
    @5
    @12
    @14
    vx
    @6
    @3
    vy
    cA
    r19.23v
    albii
    @7
    vy
    vx
    cA
    ralcom4
    @4
    @14
    vx
    @2
    @13
    @3
    vy
    @0
    cA
    eluni2
    imbi1i
    albii
    3bitr4ri
    @3
    vx
    @1
    df-ral
    @11
    @8
    vy
    cA
    @3
    vx
    @10
    df-ral
    ralbii
    3bitr4i
end
