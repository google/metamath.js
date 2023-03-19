include "cvv.mm"
include "wcel.mm"
include "wal.mm"
include "csb.mm"
include "wa.mm"
include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "abid2.mm"
include "elex.mm"
include "syl5eqel.mm"
include "alimi.mm"
include "spsbc.mm"
include "syl5.mm"
include "nfcv.mm"
include "sbcabel.mm"
include "sylibd.mm"
include "imp.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem csbexg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cW: class W
  let vy: setvar y


  assert |- ( A. x B e. W -> [_ A / x ]_ B e. _V )

  proof
    cA
    cvv
    wcel
    #
    cB
    cW
    wcel
    #
    vx
    wal
    #
    vx
    cA
    cB
    csb
    #
    cvv
    wcel
    #
    @0
    @2
    wa
    @3
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    vy
    cab
    #
    cvv
    vx
    vy
    cA
    cB
    df-csb
    @0
    @2
    @6
    cvv
    wcel
    #
    @0
    @2
    @5
    vy
    cab
    #
    cvv
    wcel
    #
    vx
    cA
    wsbc
    #
    @7
    @2
    @9
    vx
    wal
    @0
    @10
    @1
    @9
    vx
    @1
    @8
    cB
    cvv
    vy
    cB
    abid2
    cB
    cW
    elex
    syl5eqel
    alimi
    @9
    vx
    cA
    cvv
    spsbc
    syl5
    @5
    vx
    vy
    cA
    cvv
    cvv
    vx
    cvv
    nfcv
    sbcabel
    sylibd
    imp
    syl5eqel
    @0
    wn
    #
    @4
    @2
    @11
    @3
    c0
    cvv
    vx
    cA
    cB
    csbprc
    0ex
    syl6eqel
    adantr
    pm2.61ian
end
