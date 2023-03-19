include "wss.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wfr.mm"
include "sstr2.mm"
include "com12.mm"
include "anim1d.mm"
include "imim1d.mm"
include "alimdv.mm"
include "df-fr.mm"
include "3imtr4g.mm"

theorem frss
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S


  assert |- ( A C_ B -> ( R Fr B -> R Fr A ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cB
    wss
    #
    @1
    c0
    wne
    #
    wa
    #
    vz
    cv
    vy
    cv
    cR
    wbr
    wn
    vz
    @1
    wral
    vy
    @1
    wrex
    #
    wi
    #
    vx
    wal
    @1
    cA
    wss
    #
    @3
    wa
    #
    @5
    wi
    #
    vx
    wal
    cB
    cR
    wfr
    cA
    cR
    wfr
    @0
    @6
    @9
    vx
    @0
    @8
    @4
    @5
    @0
    @7
    @2
    @3
    @7
    @0
    @2
    @1
    cA
    cB
    sstr2
    com12
    anim1d
    imim1d
    alimdv
    vx
    vy
    vz
    cB
    cR
    df-fr
    vx
    vy
    vz
    cA
    cR
    df-fr
    3imtr4g
end
