include "cv.mm"
include "ccoss.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "ccnv.mm"
include "alcom.mm"
include "albii.mm"
include "wcel.mm"
include "wex.mm"
include "19.23v.mm"
include "wb.mm"
include "cvv.mm"
include "eleccossin.mm"
include "el2v.mm"
include "bicomi.mm"
include "brcoss3.mm"
include "imbi12i.mm"
include "n0.mm"
include "imbi1i.mm"
include "3bitr4i.mm"
include "2albii.mm"
include "bitri.mm"

theorem trcoss2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R

  disjoint R y
  disjoint x y
  disjoint y z
  assert |- ( A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x ,~ R z ) <-> A. x A. z ( ( [ x ] ,~ R i^i [ z ] ,~ R ) =/= (/) -> ( [ x ] `' R i^i [ z ] `' R ) =/= (/) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    ccoss
    #
    wbr
    @1
    vz
    cv
    #
    @2
    wbr
    wa
    #
    @0
    @3
    @2
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
    @6
    vy
    wal
    #
    vz
    wal
    #
    vx
    wal
    @0
    @2
    cec
    @3
    @2
    cec
    cin
    #
    c0
    wne
    #
    @0
    cR
    ccnv
    #
    cec
    @3
    @12
    cec
    cin
    c0
    wne
    #
    wi
    #
    vz
    wal
    vx
    wal
    @7
    @9
    vx
    @6
    vy
    vz
    alcom
    albii
    @8
    @14
    vx
    vz
    @1
    @10
    wcel
    #
    @13
    wi
    #
    vy
    wal
    @15
    vy
    wex
    #
    @13
    wi
    @8
    @14
    @15
    @13
    vy
    19.23v
    @6
    @16
    vy
    @4
    @15
    @5
    @13
    @15
    @4
    @15
    @4
    wb
    vy
    vz
    @0
    @1
    @3
    cR
    cvv
    cvv
    eleccossin
    el2v
    bicomi
    @5
    @13
    wb
    vx
    vz
    @0
    @3
    cR
    cvv
    cvv
    brcoss3
    el2v
    imbi12i
    albii
    @11
    @17
    @13
    vy
    @10
    n0
    imbi1i
    3bitr4i
    2albii
    bitri
end
