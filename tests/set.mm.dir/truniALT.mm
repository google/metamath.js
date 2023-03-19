include "cv.mm"
include "wtr.mm"
include "wral.mm"
include "wel.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "simpr.mm"
include "a1i.mm"
include "eluni.mm"
include "syl6ib.mm"
include "simpl.mm"
include "2a1i.mm"
include "wsbc.mm"
include "rspsbc.mm"
include "com12.mm"
include "syl6d.mm"
include "trsbc.mm"
include "biimpd.mm"
include "ee33.mm"
include "trel.mm"
include "expdcom.mm"
include "ee233.mm"
include "elunii.mm"
include "ex.mm"
include "alrimdv.mm"
include "19.23v.mm"
include "mpdd.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem truniALT
  let vx: setvar x
  let cA: class A
  let vq: setvar q
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A q
  disjoint A y
  disjoint A z
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A. x e. A Tr x -> Tr U. A )

  proof
    vx
    cv
    wtr
    #
    vx
    cA
    wral
    #
    vz
    vy
    wel
    #
    vy
    cv
    #
    cA
    cuni
    #
    wcel
    #
    wa
    #
    vz
    cv
    #
    @4
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    @4
    wtr
    @1
    @9
    vz
    vy
    @1
    @6
    vy
    vq
    wel
    #
    vq
    cv
    #
    cA
    wcel
    #
    wa
    #
    vq
    wex
    #
    @8
    @1
    @6
    @5
    @14
    @6
    @5
    wi
    @1
    @2
    @5
    simpr
    a1i
    vq
    @3
    cA
    eluni
    syl6ib
    @1
    @6
    @13
    @8
    wi
    #
    vq
    wal
    @14
    @8
    wi
    @1
    @6
    @15
    vq
    @1
    @6
    @13
    vz
    vq
    wel
    #
    @12
    @8
    @1
    @6
    @2
    @13
    @10
    @11
    wtr
    #
    @16
    @6
    @2
    wi
    @1
    @2
    @5
    simpl
    a1i
    @13
    @10
    wi
    @1
    @6
    @10
    @12
    simpl
    2a1i
    @1
    @6
    @13
    @12
    @0
    vx
    @11
    wsbc
    #
    @17
    @13
    @12
    wi
    @1
    @6
    @10
    @12
    simpr
    2a1i
    #
    @1
    @6
    @13
    @12
    @18
    @19
    @12
    @1
    @18
    @0
    vx
    @11
    cA
    rspsbc
    com12
    syl6d
    @12
    @18
    @17
    vx
    @11
    cA
    trsbc
    biimpd
    ee33
    @17
    @2
    @10
    @16
    @11
    @7
    @3
    trel
    expdcom
    ee233
    @19
    @16
    @12
    @8
    @7
    @11
    cA
    elunii
    ex
    ee33
    alrimdv
    @13
    @8
    vq
    19.23v
    syl6ib
    mpdd
    alrimivv
    vz
    vy
    @4
    dftr2
    sylibr
end
