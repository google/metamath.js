include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cnegex.mm"
include "wa.mm"
include "wrex.mm"
include "ad2antrl.mm"
include "w3a.mm"
include "0cn.mm"
include "addass.mm"
include "mp3an12.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "00id.mm"
include "oveq1i.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "addassd.mm"
include "simp2r.mm"
include "oveq1d.mm"
include "simp3r.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"
include "addid1.mm"
include "3ad2ant1.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "rexlimddv.mm"

theorem addid2
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C


  assert |- ( A e. CC -> ( 0 + A ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    vx
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    cc0
    cA
    caddc
    co
    #
    cA
    wceq
    #
    vx
    cc
    vx
    cA
    cnegex
    @0
    @1
    cc
    wcel
    #
    @3
    wa
    #
    wa
    #
    @1
    vy
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    vy
    cc
    wrex
    #
    @5
    @6
    @12
    @0
    @3
    vy
    @1
    cnegex
    ad2antrl
    @8
    @11
    @5
    vy
    cc
    @8
    @9
    cc
    wcel
    #
    @11
    @5
    @0
    @7
    @13
    @11
    wa
    #
    @5
    @0
    @7
    @14
    w3a
    #
    cc0
    cc0
    caddc
    co
    #
    @9
    caddc
    co
    #
    cc0
    cc0
    @9
    caddc
    co
    #
    caddc
    co
    #
    cA
    @4
    @14
    @0
    @17
    @19
    wceq
    #
    @7
    @13
    @20
    @11
    cc0
    cc
    wcel
    #
    @21
    @13
    @20
    0cn
    0cn
    cc0
    cc0
    @9
    addass
    mp3an12
    adantr
    3ad2ant3
    @15
    @17
    @18
    cA
    @16
    cc0
    @9
    caddc
    00id
    oveq1i
    @15
    cA
    cc0
    caddc
    co
    #
    @18
    cA
    @15
    @2
    @9
    caddc
    co
    cA
    @10
    caddc
    co
    @18
    @22
    @15
    cA
    @1
    @9
    @0
    @7
    @14
    simp1
    @0
    @6
    @3
    @14
    simp2l
    @0
    @7
    @13
    @11
    simp3l
    addassd
    @15
    @2
    cc0
    @9
    caddc
    @0
    @6
    @3
    @14
    simp2r
    oveq1d
    @15
    @10
    cc0
    cA
    caddc
    @0
    @7
    @13
    @11
    simp3r
    oveq2d
    3eqtr3rd
    @0
    @7
    @22
    cA
    wceq
    @14
    cA
    addid1
    3ad2ant1
    eqtr3d
    #
    syl5eq
    @15
    @18
    cA
    cc0
    caddc
    @23
    oveq2d
    3eqtr3rd
    3expia
    expd
    rexlimdv
    mpd
    rexlimddv
end
