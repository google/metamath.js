include "cv.mm"
include "wtr.mm"
include "wral.mm"
include "cint.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "idn2.mm"
include "simpl.mm"
include "e2.mm"
include "wsbc.mm"
include "idn3.mm"
include "idn1.mm"
include "rspsbc.mm"
include "e31.mm"
include "trsbc.mm"
include "biimpd.mm"
include "e33.mm"
include "simpr.mm"
include "elintg.mm"
include "ibi.mm"
include "rsp.mm"
include "pm2.27.mm"
include "e32.mm"
include "trel.mm"
include "expd.mm"
include "e323.mm"
include "in3.mm"
include "gen21.mm"
include "df-ral.mm"
include "biimpri.mm"
include "biimprd.mm"
include "e22.mm"
include "in2.mm"
include "gen12.mm"
include "dftr2.mm"
include "e1a.mm"
include "in1.mm"

theorem trintALTVD
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
    cA
    cint
    #
    wtr
    #
    @1
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @5
    @2
    wcel
    #
    wa
    #
    @4
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
    @8
    @9
    @1
    @8
    @6
    @4
    vq
    cv
    #
    wcel
    #
    vq
    cA
    wral
    #
    @9
    @1
    @8
    @8
    @6
    @1
    @8
    idn2
    #
    @6
    @7
    simpl
    e2
    #
    @1
    @8
    @12
    cA
    wcel
    #
    @13
    wi
    #
    vq
    wal
    #
    @14
    @1
    @8
    @18
    vq
    @1
    @8
    @17
    @13
    @1
    @8
    @17
    @12
    wtr
    #
    @6
    @5
    @12
    wcel
    #
    @13
    @1
    @8
    @17
    @17
    @0
    vx
    @12
    wsbc
    #
    @20
    @1
    @8
    @17
    idn3
    #
    @1
    @8
    @17
    @17
    @1
    @22
    @23
    @1
    idn1
    @0
    vx
    @12
    cA
    rspsbc
    e31
    @17
    @22
    @20
    vx
    @12
    cA
    trsbc
    biimpd
    e33
    @16
    @1
    @8
    @17
    @17
    @17
    @21
    wi
    #
    @21
    @23
    @1
    @8
    @21
    vq
    cA
    wral
    #
    @24
    @1
    @8
    @7
    @25
    @1
    @8
    @8
    @7
    @15
    @6
    @7
    simpr
    e2
    @7
    @25
    vq
    @5
    cA
    @2
    elintg
    ibi
    e2
    @21
    vq
    cA
    rsp
    e2
    @17
    @21
    pm2.27
    e32
    @20
    @6
    @21
    @13
    @12
    @4
    @5
    trel
    expd
    e323
    in3
    gen21
    @14
    @19
    @13
    vq
    cA
    df-ral
    biimpri
    e2
    @6
    @9
    @14
    vq
    @4
    cA
    @5
    elintg
    biimprd
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
