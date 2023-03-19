include "ccnv.mm"
include "cin.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "relin2.mm"
include "ssrel.mm"
include "mp2b.mm"
include "elin.mm"
include "df-br.mm"
include "vex.mm"
include "brcnv.mm"
include "bitr3i.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "ideq.mm"
include "imbi12i.mm"
include "2albii.mm"
include "bitri.mm"

theorem intasym
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
  assert |- ( ( R i^i `' R ) C_ _I <-> A. x A. y ( ( x R y /\ y R x ) -> x = y ) )

  proof
    cR
    cR
    ccnv
    #
    cin
    #
    cid
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @1
    wcel
    #
    @5
    cid
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @3
    @4
    cR
    wbr
    #
    @4
    @3
    cR
    wbr
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @0
    wrel
    @1
    wrel
    @2
    @9
    wb
    cR
    relcnv
    cR
    @0
    relin2
    vx
    vy
    @1
    cid
    ssrel
    mp2b
    @8
    @14
    vx
    vy
    @6
    @12
    @7
    @13
    @6
    @5
    cR
    wcel
    #
    @5
    @0
    wcel
    #
    wa
    @12
    @5
    cR
    @0
    elin
    @10
    @15
    @11
    @16
    @3
    @4
    cR
    df-br
    @11
    @3
    @4
    @0
    wbr
    @16
    @3
    @4
    cR
    vx
    vex
    vy
    vex
    #
    brcnv
    @3
    @4
    @0
    df-br
    bitr3i
    anbi12i
    bitr4i
    @7
    @3
    @4
    cid
    wbr
    @13
    @3
    @4
    cid
    df-br
    @3
    @4
    @17
    ideq
    bitr3i
    imbi12i
    2albii
    bitri
end
