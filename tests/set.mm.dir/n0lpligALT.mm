include "cplig.mm"
include "wcel.mm"
include "c0.mm"
include "wnel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "wrex.mm"
include "eqid.mm"
include "l2p.mm"
include "wi.mm"
include "noel.mm"
include "pm2.21i.mm"
include "3ad2ant2.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "syl.mm"
include "simpr.mm"
include "pm2.61danel.mm"

theorem n0lpligALT
  let cG: class G
  let va: setvar a
  let vb: setvar b


  assert |- ( G e. Plig -> (/) e/ G )

  proof
    cG
    cplig
    wcel
    #
    c0
    cG
    wnel
    #
    c0
    cG
    @0
    c0
    cG
    wcel
    wa
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    @2
    c0
    wcel
    #
    @3
    c0
    wcel
    #
    w3a
    #
    vb
    cG
    cuni
    #
    wrex
    va
    @8
    wrex
    @1
    @8
    cG
    c0
    va
    vb
    @8
    eqid
    l2p
    @7
    @1
    va
    vb
    @8
    @8
    @7
    @1
    wi
    @2
    @8
    wcel
    @3
    @8
    wcel
    wa
    @5
    @4
    @1
    @6
    @5
    @1
    @2
    noel
    pm2.21i
    3ad2ant2
    a1i
    rexlimivv
    syl
    @0
    @1
    simpr
    pm2.61danel
end
