include "wer.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "df-er.mm"
include "cnvsym.mm"
include "cotr.mm"
include "anbi12i.mm"
include "unss.mm"
include "19.28v.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"
include "bitr2i.mm"
include "3bitr3i.mm"
include "3anbi3i.mm"

theorem dfer2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  assert |- ( R Er A <-> ( Rel R /\ dom R = A /\ A. x A. y A. z ( ( x R y -> y R x ) /\ ( ( x R y /\ y R z ) -> x R z ) ) ) )

  proof
    cA
    cR
    wer
    cR
    wrel
    #
    cR
    cdm
    cA
    wceq
    #
    cR
    ccnv
    #
    cR
    cR
    ccom
    #
    cun
    cR
    wss
    #
    w3a
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @6
    @5
    cR
    wbr
    wi
    #
    @7
    @6
    vz
    cv
    #
    cR
    wbr
    wa
    @5
    @9
    cR
    wbr
    wi
    #
    wa
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    w3a
    cA
    cR
    df-er
    @4
    @13
    @0
    @1
    @2
    cR
    wss
    #
    @3
    cR
    wss
    #
    wa
    @8
    vy
    wal
    #
    vx
    wal
    #
    @10
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    wa
    #
    @4
    @13
    @14
    @17
    @15
    @20
    vx
    vy
    cR
    cnvsym
    vx
    vy
    vz
    cR
    cotr
    anbi12i
    @2
    @3
    cR
    unss
    @13
    @16
    @19
    wa
    #
    vx
    wal
    @21
    @12
    @22
    vx
    @12
    @8
    @18
    wa
    #
    vy
    wal
    @22
    @11
    @23
    vy
    @8
    @10
    vz
    19.28v
    albii
    @8
    @18
    vy
    19.26
    bitri
    albii
    @16
    @19
    vx
    19.26
    bitr2i
    3bitr3i
    3anbi3i
    bitri
end
