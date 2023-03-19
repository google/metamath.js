include "cplig.mm"
include "wcel.mm"
include "csn.mm"
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
include "wceq.mm"
include "elsni.mm"
include "weq.mm"
include "eqtr3.mm"
include "eqneqall.mm"
include "syl.mm"
include "syl2an.mm"
include "impcom.mm"
include "3impb.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "simpr.mm"
include "pm2.61danel.mm"

theorem nsnlpligALT
  let cA: class A
  let cG: class G
  let va: setvar a
  let vb: setvar b


  assert |- ( G e. Plig -> { A } e/ G )

  proof
    cG
    cplig
    wcel
    #
    cA
    csn
    #
    cG
    wnel
    #
    @1
    cG
    @0
    @1
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
    @3
    @1
    wcel
    #
    @4
    @1
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
    @9
    wrex
    @2
    @9
    cG
    @1
    va
    vb
    @9
    eqid
    l2p
    @8
    @2
    va
    vb
    @9
    @9
    @8
    @2
    wi
    @3
    @9
    wcel
    @4
    @9
    wcel
    wa
    @5
    @6
    @7
    @2
    @6
    @7
    wa
    @5
    @2
    @6
    @3
    cA
    wceq
    #
    @4
    cA
    wceq
    #
    @5
    @2
    wi
    #
    @7
    @3
    cA
    elsni
    @4
    cA
    elsni
    @10
    @11
    wa
    va
    vb
    weq
    @12
    @3
    @4
    cA
    eqtr3
    @2
    @3
    @4
    eqneqall
    syl
    syl2an
    impcom
    3impb
    a1i
    rexlimivv
    syl
    @0
    @2
    simpr
    pm2.61danel
end
