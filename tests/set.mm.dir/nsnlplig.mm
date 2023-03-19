include "cplig.mm"
include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "wrex.mm"
include "wn.mm"
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
include "pm2.01da.mm"

theorem nsnlplig
  let cA: class A
  let cG: class G
  let va: setvar a
  let vb: setvar b


  assert |- ( G e. Plig -> -. { A } e. G )

  proof
    cG
    cplig
    wcel
    #
    cA
    csn
    #
    cG
    wcel
    #
    @0
    @2
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
    wn
    #
    @9
    cG
    @1
    va
    vb
    @9
    eqid
    l2p
    @8
    @10
    va
    vb
    @9
    @9
    @8
    @10
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
    @10
    @6
    @7
    wa
    @5
    @10
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
    @10
    wi
    #
    @7
    @3
    cA
    elsni
    @4
    cA
    elsni
    @11
    @12
    wa
    va
    vb
    weq
    @13
    @3
    @4
    cA
    eqtr3
    @10
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
    pm2.01da
end
