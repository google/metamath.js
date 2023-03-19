include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cpr.mm"
include "wbr.mm"
include "coprab.mm"
include "wceq.mm"
include "elex.mm"
include "cjn.mm"
include "cfv.mm"
include "cbs.mm"
include "wa.mm"
include "fvex.mm"
include "wmo.mm"
include "moeq.mm"
include "a1i.mm"
include "eqid.mm"
include "oprabex.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "cdm.mm"
include "wfun.mm"
include "wb.mm"
include "lubfun.mm"
include "funbrfv2b.mm"
include "ax-mp.mm"
include "cple.mm"
include "simpl.mm"
include "simpr.mm"
include "lubelss.mm"
include "ex.mm"
include "vex.mm"
include "prss.mm"
include "syl6ibr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "anim12d.mm"
include "syl5bi.mm"
include "alrimiv.mm"
include "ssoprab2.mm"
include "syl.mm"
include "ssexd.mm"
include "club.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "oprabbidv.mm"
include "df-join.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "syl5eq.mm"

theorem joinfval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let vp: setvar p
  assume joinfval.u: |- U = ( lub ` K )
  assume joinfval.j: |- .\/ = ( join ` K )

  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint U z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint K p
  disjoint U p
  assert |- ( K e. V -> .\/ = { <. <. x , y >. , z >. | { x , y } U z } )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    #
    c.or
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    vz
    cv
    #
    cU
    wbr
    #
    vx
    vy
    vz
    coprab
    #
    wceq
    cK
    cV
    elex
    @0
    c.or
    cK
    cjn
    cfv
    #
    @6
    joinfval.j
    @0
    @6
    cvv
    wcel
    @7
    @6
    wceq
    @0
    @6
    @1
    cK
    cbs
    cfv
    #
    wcel
    @2
    @8
    wcel
    wa
    #
    @4
    @3
    cU
    cfv
    #
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    cvv
    @13
    cvv
    wcel
    @0
    @11
    vx
    vy
    vz
    @8
    @8
    @13
    cK
    cbs
    fvex
    #
    @14
    @11
    vz
    wmo
    @9
    vz
    @10
    moeq
    a1i
    @13
    eqid
    oprabex
    a1i
    @0
    @5
    @12
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    @6
    @13
    wss
    @0
    @17
    vx
    @0
    @16
    vy
    @0
    @15
    vz
    @5
    @3
    cU
    cdm
    wcel
    #
    @10
    @4
    wceq
    #
    wa
    #
    @0
    @12
    cU
    wfun
    @5
    @20
    wb
    cU
    cK
    joinfval.u
    lubfun
    @3
    @4
    cU
    funbrfv2b
    ax-mp
    @0
    @18
    @9
    @19
    @11
    @0
    @18
    @3
    @8
    wss
    #
    @9
    @0
    @18
    @21
    @0
    @18
    wa
    @8
    @3
    cU
    cK
    cK
    cple
    cfv
    #
    cvv
    @8
    eqid
    @22
    eqid
    joinfval.u
    @0
    @18
    simpl
    @0
    @18
    simpr
    lubelss
    ex
    @1
    @2
    @8
    vx
    vex
    vy
    vex
    prss
    syl6ibr
    @19
    @11
    wi
    @0
    @19
    @11
    @10
    @4
    eqcom
    biimpi
    a1i
    anim12d
    syl5bi
    alrimiv
    alrimiv
    alrimiv
    @5
    @12
    vx
    vy
    vz
    ssoprab2
    syl
    ssexd
    vp
    cK
    @3
    @4
    vp
    cv
    #
    club
    cfv
    #
    wbr
    #
    vx
    vy
    vz
    coprab
    @6
    cvv
    cvv
    cjn
    @23
    cK
    wceq
    #
    @25
    @5
    vx
    vy
    vz
    @26
    @24
    cU
    @3
    @4
    @26
    @24
    cK
    club
    cfv
    cU
    @23
    cK
    club
    fveq2
    joinfval.u
    syl6eqr
    breqd
    oprabbidv
    vx
    vy
    vz
    vp
    df-join
    fvmptg
    mpdan
    syl5eq
    syl
end
