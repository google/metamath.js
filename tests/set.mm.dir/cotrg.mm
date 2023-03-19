include "ccom.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wbr.mm"
include "wa.mm"
include "wrel.mm"
include "wb.mm"
include "wex.mm"
include "df-co.mm"
include "relopabi.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "vex.mm"
include "opelco.mm"
include "df-br.mm"
include "bicomi.mm"
include "imbi12i.mm"
include "19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "alcom.mm"
include "bitri.mm"

theorem cotrg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  assert |- ( ( A o. B ) C_ C <-> A. x A. y A. z ( ( x B y /\ y A z ) -> x C z ) )

  proof
    cA
    cB
    ccom
    #
    cC
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    cop
    #
    @0
    wcel
    #
    @4
    cC
    wcel
    #
    wi
    #
    vz
    wal
    #
    vx
    wal
    #
    @2
    vy
    cv
    #
    cB
    wbr
    @10
    @3
    cA
    wbr
    wa
    #
    @2
    @3
    cC
    wbr
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    @0
    wrel
    @1
    @9
    wb
    @11
    vy
    wex
    #
    vx
    vz
    @0
    vx
    vz
    vy
    cA
    cB
    df-co
    relopabi
    vx
    vz
    @0
    cC
    ssrel
    ax-mp
    @8
    @14
    vx
    @8
    @13
    vy
    wal
    #
    vz
    wal
    @14
    @7
    @16
    vz
    @7
    @15
    @12
    wi
    @16
    @5
    @15
    @6
    @12
    vy
    @2
    @3
    cA
    cB
    vx
    vex
    vz
    vex
    opelco
    @12
    @6
    @2
    @3
    cC
    df-br
    bicomi
    imbi12i
    @11
    @12
    vy
    19.23v
    bitr4i
    albii
    @13
    vz
    vy
    alcom
    bitri
    albii
    bitri
end
