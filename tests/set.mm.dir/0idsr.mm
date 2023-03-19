include "cv.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "c0r.mm"
include "cplr.mm"
include "co.mm"
include "wceq.mm"
include "cnp.mm"
include "cnr.mm"
include "df-nr.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "wa.mm"
include "c1p.mm"
include "df-0r.mm"
include "oveq2i.mm"
include "cpp.mm"
include "1pr.mm"
include "addsrpr.mm"
include "mpanr12.mm"
include "addclpr.mm"
include "mpan2.mm"
include "anim12i.mm"
include "vex.mm"
include "elexi.mm"
include "addcompr.mm"
include "addasspr.mm"
include "caov12.mm"
include "enreceq.mm"
include "mpbiri.mm"
include "mpdan.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "ecoptocl.mm"

theorem 0idsr
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( A e. R. -> ( A +R 0R ) = A )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    cer
    cec
    #
    c0r
    cplr
    co
    #
    @2
    wceq
    cA
    c0r
    cplr
    co
    #
    cA
    wceq
    vx
    vy
    cA
    cnp
    cnp
    cer
    cnr
    df-nr
    @2
    cA
    wceq
    #
    @3
    @4
    @2
    cA
    @2
    cA
    c0r
    cplr
    oveq1
    @5
    id
    eqeq12d
    @0
    cnp
    wcel
    #
    @1
    cnp
    wcel
    #
    wa
    #
    @3
    @2
    c1p
    c1p
    cop
    cer
    cec
    #
    cplr
    co
    #
    @2
    c0r
    @9
    @2
    cplr
    df-0r
    oveq2i
    @8
    @10
    @0
    c1p
    cpp
    co
    #
    @1
    c1p
    cpp
    co
    #
    cop
    cer
    cec
    #
    @2
    @8
    c1p
    cnp
    wcel
    #
    @14
    @10
    @13
    wceq
    1pr
    1pr
    @0
    @1
    c1p
    c1p
    addsrpr
    mpanr12
    @8
    @11
    cnp
    wcel
    #
    @12
    cnp
    wcel
    #
    wa
    #
    @2
    @13
    wceq
    #
    @6
    @15
    @7
    @16
    @6
    @14
    @15
    1pr
    @0
    c1p
    addclpr
    mpan2
    @7
    @14
    @16
    1pr
    @1
    c1p
    addclpr
    mpan2
    anim12i
    @8
    @17
    wa
    @18
    @0
    @12
    cpp
    co
    @1
    @11
    cpp
    co
    wceq
    vz
    vw
    vv
    @0
    @1
    c1p
    cpp
    vx
    vex
    vy
    vex
    c1p
    cnp
    1pr
    elexi
    vz
    cv
    #
    vw
    cv
    #
    addcompr
    @19
    @20
    vv
    cv
    addasspr
    caov12
    @0
    @1
    @11
    @12
    enreceq
    mpbiri
    mpdan
    eqtr4d
    syl5eq
    ecoptocl
end
