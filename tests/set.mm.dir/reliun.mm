include "ciun.mm"
include "wrel.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wral.mm"
include "df-iun.mm"
include "releqi.mm"
include "df-rel.mm"
include "wi.mm"
include "wal.mm"
include "abss.mm"
include "dfss2.mm"
include "bitri.mm"
include "ralbii.mm"
include "ralcom4.mm"
include "r19.23v.mm"
include "albii.mm"
include "3bitri.mm"
include "bitr4i.mm"

theorem reliun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( Rel U_ x e. A B <-> A. x e. A Rel B )

  proof
    vx
    cA
    cB
    ciun
    #
    wrel
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    wrel
    @4
    cvv
    cvv
    cxp
    #
    wss
    #
    cB
    wrel
    #
    vx
    cA
    wral
    #
    @0
    @4
    vx
    vy
    cA
    cB
    df-iun
    releqi
    @4
    df-rel
    @6
    @3
    @1
    @5
    wcel
    #
    wi
    #
    vy
    wal
    #
    @8
    @3
    vy
    @5
    abss
    @8
    @2
    @9
    wi
    #
    vy
    wal
    #
    vx
    cA
    wral
    @12
    vx
    cA
    wral
    #
    vy
    wal
    @11
    @7
    @13
    vx
    cA
    @7
    cB
    @5
    wss
    @13
    cB
    df-rel
    vy
    cB
    @5
    dfss2
    bitri
    ralbii
    @12
    vx
    vy
    cA
    ralcom4
    @14
    @10
    vy
    @2
    @9
    vx
    cA
    r19.23v
    albii
    3bitri
    bitr4i
    3bitri
end
