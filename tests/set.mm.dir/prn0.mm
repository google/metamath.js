include "cnp.mm"
include "wcel.mm"
include "c0.mm"
include "wpss.mm"
include "wne.mm"
include "cvv.mm"
include "cnq.mm"
include "w3a.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "elnpi.mm"
include "simpl2.mm"
include "sylbi.mm"
include "0pss.mm"
include "sylib.mm"

theorem prn0
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. P. -> A =/= (/) )

  proof
    cA
    cnp
    wcel
    #
    c0
    cA
    wpss
    #
    cA
    c0
    wne
    @0
    cA
    cvv
    wcel
    #
    @1
    cA
    cnq
    wpss
    #
    w3a
    vy
    cv
    #
    vx
    cv
    #
    cltq
    wbr
    @4
    cA
    wcel
    wi
    vy
    wal
    @5
    @4
    cltq
    wbr
    vy
    cA
    wrex
    wa
    vx
    cA
    wral
    #
    wa
    @1
    vx
    vy
    cA
    elnpi
    @2
    @1
    @3
    @6
    simpl2
    sylbi
    cA
    0pss
    sylib
end
