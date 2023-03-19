include "cv.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cep.mm"
include "wfr.mm"
include "idn1.mm"
include "simpr.mm"
include "e1a.mm"
include "wcel.mm"
include "wex.mm"
include "wb.mm"
include "wn.mm"
include "wo.mm"
include "exmid.mm"
include "onfrALTlem1VD.mm"
include "in2an.mm"
include "onfrALTlem2VD.mm"
include "pm2.61.mm"
include "a1i.mm"
include "e022.mm"
include "in2.mm"
include "gen11.mm"
include "19.23v.mm"
include "biimpi.mm"
include "n0.mm"
include "imbi1.mm"
include "biimprcd.mm"
include "e10.mm"
include "pm2.27.mm"
include "e11.mm"
include "in1.mm"
include "ax-gen.mm"
include "dfepfr.mm"
include "biimpri.mm"
include "e0a.mm"

theorem onfrALTVD
  let va: setvar a
  let vx: setvar x
  let vy: setvar y


  assert |- _E Fr On

  proof
    va
    cv
    #
    con0
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    @0
    vy
    cv
    cin
    c0
    wceq
    vy
    @0
    wrex
    #
    wi
    #
    va
    wal
    #
    con0
    cep
    wfr
    #
    @5
    va
    @3
    @4
    @3
    @2
    @2
    @4
    wi
    #
    @4
    @3
    @3
    @2
    @3
    idn1
    @1
    @2
    simpr
    e1a
    @3
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    #
    @4
    wi
    #
    @2
    @11
    wb
    #
    @8
    @3
    @10
    @4
    wi
    #
    vx
    wal
    #
    @12
    @3
    @14
    vx
    @3
    @10
    @4
    @0
    @9
    cin
    c0
    wceq
    #
    @16
    wn
    #
    wo
    #
    @3
    @10
    @16
    @4
    wi
    #
    @17
    @4
    wi
    #
    @4
    @16
    exmid
    @3
    @10
    @16
    @4
    vx
    vy
    va
    onfrALTlem1VD
    in2an
    @3
    @10
    @17
    @4
    vx
    vy
    va
    onfrALTlem2VD
    in2an
    @19
    @20
    @4
    wi
    wi
    @18
    @16
    @4
    pm2.61
    a1i
    e022
    in2
    gen11
    @15
    @12
    @10
    @4
    vx
    19.23v
    biimpi
    e1a
    vx
    @0
    n0
    @13
    @8
    @12
    @2
    @11
    @4
    imbi1
    biimprcd
    e10
    @2
    @4
    pm2.27
    e11
    in1
    ax-gen
    @7
    @6
    va
    vy
    con0
    dfepfr
    biimpri
    e0a
end
