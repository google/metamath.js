include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "csb.mm"
include "wceq.mm"
include "wel.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbcex2.mm"
include "sbcan.mm"
include "sbcg.mm"
include "anbi1d.mm"
include "sbcel2.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "exbidv.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "df-uni.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbuni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z


  assert |- [_ A / x ]_ U. B = U. [_ A / x ]_ B

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    cuni
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    cuni
    #
    wceq
    @0
    vx
    cA
    vz
    vy
    wel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    vz
    cab
    #
    csb
    #
    @5
    @6
    @3
    wcel
    #
    wa
    #
    vy
    wex
    #
    vz
    cab
    #
    @2
    @4
    @0
    @11
    @9
    vx
    cA
    wsbc
    #
    vz
    cab
    @15
    @9
    vx
    vz
    cA
    csbab
    @0
    @16
    @14
    vz
    @16
    @8
    vx
    cA
    wsbc
    #
    vy
    wex
    @0
    @14
    @8
    vy
    vx
    cA
    sbcex2
    @0
    @17
    @13
    vy
    @17
    @5
    vx
    cA
    wsbc
    #
    @7
    vx
    cA
    wsbc
    #
    wa
    #
    @0
    @13
    @5
    @7
    vx
    cA
    sbcan
    @0
    @20
    @5
    @19
    wa
    @13
    @0
    @18
    @5
    @19
    @5
    vx
    cA
    cvv
    sbcg
    anbi1d
    @19
    @12
    @5
    vx
    cA
    @6
    cB
    sbcel2
    anbi2i
    syl6bb
    syl5bb
    exbidv
    syl5bb
    abbidv
    syl5eq
    vx
    cA
    @1
    @10
    vz
    vy
    cB
    df-uni
    csbeq2i
    vz
    vy
    @3
    df-uni
    3eqtr4g
    @0
    wn
    #
    @2
    c0
    @4
    vx
    cA
    @1
    csbprc
    @21
    @4
    c0
    cuni
    c0
    @21
    @3
    c0
    vx
    cA
    cB
    csbprc
    unieqd
    uni0
    syl6req
    eqtrd
    pm2.61i
end
