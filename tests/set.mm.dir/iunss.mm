include "ciun.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-iun.mm"
include "sseq1i.mm"
include "abss.mm"
include "dfss2.mm"
include "ralbii.mm"
include "ralcom4.mm"
include "r19.23v.mm"
include "albii.mm"
include "3bitrri.mm"
include "3bitri.mm"

theorem iunss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint C x
  disjoint x y
  disjoint C y
  disjoint A y
  disjoint B y
  assert |- ( U_ x e. A B C_ C <-> A. x e. A B C_ C )

  proof
    vx
    cA
    cB
    ciun
    #
    cC
    wss
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
    cC
    wss
    @3
    @1
    cC
    wcel
    #
    wi
    #
    vy
    wal
    #
    cB
    cC
    wss
    #
    vx
    cA
    wral
    #
    @0
    @4
    cC
    vx
    vy
    cA
    cB
    df-iun
    sseq1i
    @3
    vy
    cC
    abss
    @9
    @2
    @5
    wi
    #
    vy
    wal
    #
    vx
    cA
    wral
    @10
    vx
    cA
    wral
    #
    vy
    wal
    @7
    @8
    @11
    vx
    cA
    vy
    cB
    cC
    dfss2
    ralbii
    @10
    vx
    vy
    cA
    ralcom4
    @12
    @6
    vy
    @2
    @5
    vx
    cA
    r19.23v
    albii
    3bitrri
    3bitri
end
