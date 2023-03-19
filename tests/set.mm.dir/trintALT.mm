include "cv.mm"
include "wtr.mm"
include "wral.mm"
include "wel.mm"
include "cint.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "simpl.mm"
include "a1i.mm"
include "wsbc.mm"
include "iidn3.mm"
include "id.mm"
include "rspsbc.mm"
include "ee31.mm"
include "trsbc.mm"
include "biimpd.mm"
include "ee33.mm"
include "simpr.mm"
include "elintg.mm"
include "ibi.mm"
include "syl6.mm"
include "rsp.mm"
include "trel.mm"
include "expd.mm"
include "ee323.mm"
include "ralrimdv.mm"
include "biimprd.mm"
include "syl6c.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"

theorem trintALT
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
  assert |- ( A. x e. A Tr x -> Tr |^| A )

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
    cint
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
    @2
    vz
    vq
    wel
    #
    vq
    cA
    wral
    #
    @8
    @6
    @2
    wi
    @1
    @2
    @5
    simpl
    a1i
    #
    @1
    @6
    @10
    vq
    cA
    @1
    @6
    vq
    cv
    #
    cA
    wcel
    #
    @13
    wtr
    #
    @2
    vy
    vq
    wel
    #
    @10
    @1
    @6
    @14
    @14
    @0
    vx
    @13
    wsbc
    #
    @15
    @1
    @6
    @14
    iidn3
    #
    @1
    @6
    @14
    @14
    @1
    @17
    @18
    @1
    id
    @0
    vx
    @13
    cA
    rspsbc
    ee31
    @14
    @17
    @15
    vx
    @13
    cA
    trsbc
    biimpd
    ee33
    @12
    @1
    @6
    @16
    vq
    cA
    wral
    #
    @14
    @16
    wi
    @1
    @6
    @5
    @19
    @6
    @5
    wi
    @1
    @2
    @5
    simpr
    a1i
    @5
    @19
    vq
    @3
    cA
    @4
    elintg
    ibi
    syl6
    @16
    vq
    cA
    rsp
    syl6
    @15
    @2
    @16
    @10
    @13
    @7
    @3
    trel
    expd
    ee323
    ralrimdv
    @2
    @8
    @11
    vq
    @7
    cA
    @3
    elintg
    biimprd
    syl6c
    alrimivv
    vz
    vy
    @4
    dftr2
    sylibr
end
