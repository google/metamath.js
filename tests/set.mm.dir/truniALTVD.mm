include "cv.mm"
include "wtr.mm"
include "wral.mm"
include "cuni.mm"
include "wel.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "idn2.mm"
include "simpr.mm"
include "e2.mm"
include "eluni.mm"
include "biimpi.mm"
include "simpl.mm"
include "idn3.mm"
include "e3.mm"
include "wsbc.mm"
include "idn1.mm"
include "rspsbc.mm"
include "com12.mm"
include "e13.mm"
include "trsbc.mm"
include "biimpd.mm"
include "e33.mm"
include "trel.mm"
include "expdcom.mm"
include "e233.mm"
include "elunii.mm"
include "ex.mm"
include "in3.mm"
include "gen21.mm"
include "19.23v.mm"
include "pm2.27.mm"
include "e22.mm"
include "in2.mm"
include "gen12.mm"
include "dftr2.mm"
include "biimpri.mm"
include "e1a.mm"
include "in1.mm"

theorem truniALTVD
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
    cA
    cuni
    #
    wtr
    #
    @1
    vz
    vy
    wel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    vz
    cv
    #
    @2
    wcel
    #
    wi
    #
    vy
    wal
    vz
    wal
    #
    @3
    @1
    @10
    vz
    vy
    @1
    @7
    @9
    @1
    @7
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
    @16
    @9
    wi
    #
    @9
    @1
    @7
    @6
    @16
    @1
    @7
    @7
    @6
    @1
    @7
    idn2
    #
    @4
    @6
    simpr
    e2
    @6
    @16
    vq
    @5
    cA
    eluni
    biimpi
    e2
    @1
    @7
    @15
    @9
    wi
    #
    vq
    wal
    #
    @17
    @1
    @7
    @19
    vq
    @1
    @7
    @15
    @9
    @1
    @7
    @15
    vz
    vq
    wel
    #
    @14
    @9
    @1
    @7
    @4
    @15
    @12
    @13
    wtr
    #
    @21
    @1
    @7
    @7
    @4
    @18
    @4
    @6
    simpl
    e2
    @1
    @7
    @15
    @15
    @12
    @1
    @7
    @15
    idn3
    #
    @12
    @14
    simpl
    e3
    @1
    @7
    @15
    @14
    @0
    vx
    @13
    wsbc
    #
    @22
    @1
    @7
    @15
    @15
    @14
    @23
    @12
    @14
    simpr
    e3
    #
    @1
    @1
    @7
    @15
    @14
    @24
    @1
    idn1
    @25
    @14
    @1
    @24
    @0
    vx
    @13
    cA
    rspsbc
    com12
    e13
    @14
    @24
    @22
    vx
    @13
    cA
    trsbc
    biimpd
    e33
    @22
    @4
    @12
    @21
    @13
    @8
    @5
    trel
    expdcom
    e233
    @25
    @21
    @14
    @9
    @8
    @13
    cA
    elunii
    ex
    e33
    in3
    gen21
    @20
    @17
    @15
    @9
    vq
    19.23v
    biimpi
    e2
    @16
    @9
    pm2.27
    e22
    in2
    gen12
    @3
    @11
    vz
    vy
    @2
    dftr2
    biimpri
    e1a
    in1
end
