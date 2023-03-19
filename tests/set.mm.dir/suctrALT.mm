include "wtr.mm"
include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "w3a.mm"
include "sssucid.mm"
include "id.mm"
include "simpld.mm"
include "trel.mm"
include "3impib.mm"
include "idiALT.mm"
include "syl3an.mm"
include "sseldi.mm"
include "3expia.mm"
include "adantr.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "ex.mm"
include "wo.mm"
include "simprd.mm"
include "elsuci.mm"
include "syl.mm"
include "mpjaod.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "biimpri.mm"

theorem suctrALT
  let cA: class A
  let vy: setvar y
  let vz: setvar z


  assert |- ( Tr A -> Tr suc A )

  proof
    cA
    wtr
    #
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @2
    cA
    csuc
    #
    wcel
    #
    wa
    #
    @1
    @4
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    #
    @4
    wtr
    #
    @0
    @8
    vz
    vy
    @0
    @6
    @7
    @0
    @6
    wa
    @2
    cA
    wcel
    #
    @7
    @2
    cA
    wceq
    #
    @0
    @6
    @11
    @7
    @0
    @6
    @11
    w3a
    cA
    @4
    @1
    cA
    sssucid
    #
    @0
    @0
    @6
    @3
    @11
    @11
    @1
    cA
    wcel
    #
    @0
    id
    @6
    @3
    @5
    @6
    id
    #
    simpld
    #
    @11
    id
    @0
    @3
    @11
    w3a
    @14
    wi
    @0
    @3
    @11
    @14
    cA
    @1
    @2
    trel
    3impib
    idiALT
    syl3an
    sseldi
    3expia
    @6
    @12
    @7
    wi
    @0
    @6
    @12
    @7
    @6
    @12
    wa
    #
    cA
    @4
    @1
    @13
    @17
    @1
    @2
    cA
    @6
    @3
    @12
    @16
    adantr
    @12
    @12
    @6
    @12
    id
    adantl
    eleqtrd
    sseldi
    ex
    adantl
    @6
    @11
    @12
    wo
    #
    @0
    @6
    @5
    @18
    @6
    @3
    @5
    @15
    simprd
    @2
    cA
    elsuci
    syl
    adantl
    mpjaod
    ex
    alrimivv
    @10
    @9
    vz
    vy
    @4
    dftr2
    biimpri
    syl
end
