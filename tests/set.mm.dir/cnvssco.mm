include "cv.mm"
include "cop.mm"
include "ccnv.mm"
include "wcel.mm"
include "ccom.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "alcom.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "19.37v.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "bitr3i.mm"
include "brco.mm"
include "imbi12i.mm"
include "bitri.mm"
include "2albii.mm"
include "3bitr4i.mm"

theorem cnvssco
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
  assert |- ( `' A C_ `' ( B o. C ) <-> A. x A. y E. z ( x A y -> ( x C z /\ z B y ) ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    cA
    ccnv
    #
    wcel
    #
    @2
    cB
    cC
    ccom
    #
    ccnv
    #
    wcel
    #
    wi
    #
    vx
    wal
    vy
    wal
    #
    @8
    vy
    wal
    vx
    wal
    @3
    @6
    wss
    #
    @1
    @0
    cA
    wbr
    #
    @1
    vz
    cv
    #
    cC
    wbr
    @12
    @0
    cB
    wbr
    wa
    #
    wi
    vz
    wex
    #
    vy
    wal
    vx
    wal
    @8
    vy
    vx
    alcom
    @3
    wrel
    @10
    @9
    wb
    cA
    relcnv
    vy
    vx
    @3
    @6
    ssrel
    ax-mp
    @14
    @8
    vx
    vy
    @14
    @11
    @13
    vz
    wex
    #
    wi
    @8
    @11
    @13
    vz
    19.37v
    @11
    @4
    @15
    @7
    @11
    @0
    @1
    @3
    wbr
    @4
    @0
    @1
    cA
    vy
    vex
    #
    vx
    vex
    #
    brcnv
    @0
    @1
    @3
    df-br
    bitr3i
    @15
    @1
    @0
    @5
    wbr
    #
    @7
    vz
    @1
    @0
    cB
    cC
    @17
    @16
    brco
    @18
    @0
    @1
    @6
    wbr
    @7
    @0
    @1
    @5
    @16
    @17
    brcnv
    @0
    @1
    @6
    df-br
    bitr3i
    bitr3i
    imbi12i
    bitri
    2albii
    3bitr4i
end
