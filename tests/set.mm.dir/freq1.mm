include "wceq.mm"
include "cv.mm"
include "wss.mm"
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
include "breq.mm"
include "notbid.mm"
include "rexralbidv.mm"
include "imbi2d.mm"
include "albidv.mm"
include "df-fr.mm"
include "3bitr4g.mm"

theorem freq1
  let cA: class A
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R = S -> ( R Fr A <-> S Fr A ) )

  proof
    cR
    cS
    wceq
    #
    vx
    cv
    #
    cA
    wss
    @1
    c0
    wne
    wa
    #
    vz
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
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
    @2
    @3
    @4
    cS
    wbr
    #
    wn
    #
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
    cA
    cR
    wfr
    cA
    cS
    wfr
    @0
    @8
    @12
    vx
    @0
    @7
    @11
    @2
    @0
    @6
    @10
    vy
    vz
    @1
    @1
    @0
    @5
    @9
    @3
    @4
    cR
    cS
    breq
    notbid
    rexralbidv
    imbi2d
    albidv
    vx
    vy
    vz
    cA
    cR
    df-fr
    vx
    vy
    vz
    cA
    cS
    df-fr
    3bitr4g
end
