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
include "idn1.mm"
include "simpl.mm"
include "el1.mm"
include "trel.mm"
include "3impib.mm"
include "el123.mm"
include "ssel2.mm"
include "el0321old.mm"
include "int3.mm"
include "eleq2.mm"
include "biimpac.mm"
include "el12.mm"
include "el021old.mm"
include "int2.mm"
include "simpr.mm"
include "elsuci.mm"
include "jao.mm"
include "3imp.mm"
include "el2122old.mm"
include "gen12.mm"
include "dftr2.mm"
include "biimpri.mm"
include "in1.mm"

theorem suctrALTcfVD
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
    idn1
    @7
    @7
    @5
    @7
    idn1
    #
    @5
    @6
    simpl
    el1
    #
    @11
    idn1
    @0
    @5
    @11
    @17
    cA
    @3
    @4
    trel
    3impib
    el123
    cA
    @1
    @3
    ssel2
    #
    el0321old
    int3
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
    idn1
    @13
    @5
    @17
    @4
    cA
    @3
    eleq2
    biimpac
    el12
    @21
    el021old
    int2
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
    el1
    @4
    cA
    elsuci
    el1
    @12
    @14
    @15
    @8
    @11
    @8
    @13
    jao
    3imp
    el2122old
    int2
    gen12
    @2
    @10
    vz
    vy
    @1
    dftr2
    biimpri
    el1
    in1
end
