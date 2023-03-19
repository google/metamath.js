include "wtr.mm"
include "csuc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "sssucid.mm"
include "id.mm"
include "simpl.mm"
include "syl.mm"
include "trel.mm"
include "3impib.mm"
include "syl3an.mm"
include "ssel2.mm"
include "eel0321old.mm"
include "3expia.mm"
include "eleq2.mm"
include "biimpac.mm"
include "syl2an.mm"
include "eel021old.mm"
include "ex.mm"
include "simpr.mm"
include "elsuci.mm"
include "jao.mm"
include "3imp.mm"
include "eel2122old.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "biimpri.mm"
include "iin1.mm"

theorem suctrALTcf
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
    @4
    cA
    wcel
    #
    @8
    wi
    #
    @4
    cA
    wceq
    #
    @8
    wi
    #
    @11
    @13
    wo
    #
    @8
    @0
    @7
    @11
    @8
    cA
    @1
    wss
    #
    @0
    @7
    @11
    @3
    cA
    wcel
    #
    @8
    cA
    sssucid
    #
    @0
    @0
    @7
    @5
    @11
    @11
    @17
    @0
    id
    @7
    @7
    @5
    @7
    id
    #
    @5
    @6
    simpl
    syl
    #
    @11
    id
    @0
    @5
    @11
    @17
    cA
    @3
    @4
    trel
    3impib
    syl3an
    cA
    @1
    @3
    ssel2
    #
    eel0321old
    3expia
    @7
    @13
    @8
    @16
    @7
    @13
    @17
    @8
    @18
    @7
    @5
    @13
    @17
    @13
    @20
    @13
    id
    @13
    @5
    @17
    @4
    cA
    @3
    eleq2
    biimpac
    syl2an
    @21
    eel021old
    ex
    @7
    @6
    @15
    @7
    @7
    @6
    @19
    @5
    @6
    simpr
    syl
    @4
    cA
    elsuci
    syl
    @12
    @14
    @15
    @8
    @11
    @8
    @13
    jao
    3imp
    eel2122old
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
    iin1
end
