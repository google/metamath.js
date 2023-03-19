include "cvv.mm"
include "wcel.mm"
include "ctc.mm"
include "cfv.mm"
include "wtr.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "trint.mm"
include "vex.mm"
include "wceq.mm"
include "sseq2.mm"
include "treq.mm"
include "anbi12d.mm"
include "elab.mm"
include "simprbi.mm"
include "mprg.mm"
include "wb.mm"
include "tcvalg.mm"
include "syl.mm"
include "mpbiri.mm"
include "wn.mm"
include "c0.mm"
include "tr0.mm"
include "fvprc.mm"
include "pm2.61i.mm"

theorem tctr
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- Tr ( TC ` A )

  proof
    cA
    cvv
    wcel
    #
    cA
    ctc
    cfv
    #
    wtr
    #
    @0
    @2
    cA
    vx
    cv
    #
    wss
    #
    @3
    wtr
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    wtr
    #
    vy
    cv
    #
    wtr
    #
    @9
    vy
    @7
    vy
    @7
    trint
    @10
    @7
    wcel
    cA
    @10
    wss
    #
    @11
    @6
    @12
    @11
    wa
    vx
    @10
    vy
    vex
    @3
    @10
    wceq
    @4
    @12
    @5
    @11
    @3
    @10
    cA
    sseq2
    @3
    @10
    treq
    anbi12d
    elab
    simprbi
    mprg
    @0
    @1
    @8
    wceq
    @2
    @9
    wb
    vx
    cA
    cvv
    tcvalg
    @1
    @8
    treq
    syl
    mpbiri
    @0
    wn
    #
    @2
    c0
    wtr
    #
    tr0
    @13
    @1
    c0
    wceq
    @2
    @14
    wb
    cA
    ctc
    fvprc
    @1
    c0
    treq
    syl
    mpbiri
    pm2.61i
end
