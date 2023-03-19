include "cv.mm"
include "cop.mm"
include "ccnv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wbr.mm"
include "alcom.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "bitr3i.mm"
include "imbi12i.mm"
include "2albii.mm"
include "3bitr4i.mm"

theorem cnvsym
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V z
  disjoint W z
  assert |- ( `' R C_ R <-> A. x A. y ( x R y -> y R x ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    cR
    ccnv
    #
    wcel
    #
    @2
    cR
    wcel
    #
    wi
    #
    vx
    wal
    vy
    wal
    #
    @6
    vy
    wal
    vx
    wal
    @3
    cR
    wss
    #
    @1
    @0
    cR
    wbr
    #
    @0
    @1
    cR
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    @6
    vy
    vx
    alcom
    @3
    wrel
    @8
    @7
    wb
    cR
    relcnv
    vy
    vx
    @3
    cR
    ssrel
    ax-mp
    @11
    @6
    vx
    vy
    @9
    @4
    @10
    @5
    @9
    @0
    @1
    @3
    wbr
    @4
    @0
    @1
    cR
    vy
    vex
    vx
    vex
    brcnv
    @0
    @1
    @3
    df-br
    bitr3i
    @0
    @1
    cR
    df-br
    imbi12i
    2albii
    3bitr4i
end
