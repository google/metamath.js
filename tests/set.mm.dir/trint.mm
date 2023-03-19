include "cv.mm"
include "wtr.mm"
include "wral.mm"
include "wel.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cint.mm"
include "dftr3.mm"
include "ralbii.mm"
include "df-ral.mm"
include "ralcom4.mm"
include "bitri.mm"
include "sylbb.mm"
include "ralim.mm"
include "sylg.mm"
include "wcel.mm"
include "vex.mm"
include "elint2.mm"
include "ssint.mm"
include "imbi12i.mm"
include "albii.mm"
include "sylibr.mm"

theorem trint
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. A Tr x -> Tr |^| A )

  proof
    vx
    cv
    #
    wtr
    #
    vx
    cA
    wral
    #
    vy
    vx
    wel
    #
    vx
    cA
    wral
    #
    vy
    cv
    #
    @0
    wss
    #
    vx
    cA
    wral
    #
    wi
    #
    vy
    wal
    #
    cA
    cint
    #
    wtr
    #
    @2
    @3
    @6
    wi
    #
    vx
    cA
    wral
    #
    @8
    vy
    @2
    @6
    vy
    @0
    wral
    #
    vx
    cA
    wral
    #
    @13
    vy
    wal
    #
    @1
    @14
    vx
    cA
    vy
    @0
    dftr3
    ralbii
    @15
    @12
    vy
    wal
    #
    vx
    cA
    wral
    @16
    @14
    @17
    vx
    cA
    @6
    vy
    @0
    df-ral
    ralbii
    @12
    vx
    vy
    cA
    ralcom4
    bitri
    sylbb
    @3
    @6
    vx
    cA
    ralim
    sylg
    @11
    @5
    @10
    wss
    #
    vy
    @10
    wral
    #
    @9
    vy
    @10
    dftr3
    @19
    @5
    @10
    wcel
    #
    @18
    wi
    #
    vy
    wal
    @9
    @18
    vy
    @10
    df-ral
    @21
    @8
    vy
    @20
    @4
    @18
    @7
    vx
    @5
    cA
    vy
    vex
    elint2
    vx
    @5
    cA
    ssint
    imbi12i
    albii
    bitri
    bitri
    sylibr
end
