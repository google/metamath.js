include "wtr.mm"
include "csuc.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wal.mm"
include "wceq.mm"
include "w3a.mm"
include "sssucid.mm"
include "id.mm"
include "simpld.mm"
include "trelded.mm"
include "sseldi.mm"
include "3expia.mm"
include "eleq2.mm"
include "biimpac.mm"
include "syl2an.mm"
include "ex.mm"
include "wo.mm"
include "simprd.mm"
include "elsuci.mm"
include "syl.mm"
include "jaoded.mm"
include "un2122.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "biimpri.mm"
include "idiALT.mm"

theorem suctrALT3
  let cA: class A
  let vz: setvar z
  let vy: setvar y


  assert |- ( Tr A -> Tr suc A )

  proof
    cA
    wtr
    #
    cA
    csuc
    #
    wtr
    #
    wi
    @0
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @3
    @1
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    #
    @2
    @0
    @9
    vz
    vy
    @0
    @7
    @8
    @0
    @7
    @8
    @0
    @7
    wa
    @4
    cA
    wcel
    #
    @8
    @7
    @4
    cA
    wceq
    #
    @7
    @0
    @7
    @11
    @8
    @0
    @7
    @11
    w3a
    cA
    @1
    @3
    cA
    sssucid
    #
    @0
    @7
    @11
    cA
    @3
    @4
    @0
    id
    @7
    @5
    @6
    @7
    id
    #
    simpld
    #
    @11
    id
    trelded
    sseldi
    3expia
    @7
    @12
    @8
    @7
    @12
    wa
    cA
    @1
    @3
    @13
    @7
    @5
    @12
    @3
    cA
    wcel
    #
    @12
    @15
    @12
    id
    @12
    @5
    @16
    @4
    cA
    @3
    eleq2
    biimpac
    syl2an
    sseldi
    ex
    @7
    @6
    @11
    @12
    wo
    @7
    @5
    @6
    @14
    simprd
    @4
    cA
    elsuci
    syl
    jaoded
    un2122
    ex
    alrimivv
    @2
    @10
    vz
    vy
    @1
    dftr2
    biimpri
    syl
    idiALT
end
