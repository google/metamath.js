include "cnp.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
include "wpss.mm"
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
include "simpl3.mm"
include "sylbi.mm"

theorem prpssnq
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. P. -> A C. Q. )

  proof
    cA
    cnp
    wcel
    cA
    cvv
    wcel
    #
    c0
    cA
    wpss
    #
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
    @3
    cA
    wcel
    wi
    vy
    wal
    @4
    @3
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
    @2
    vx
    vy
    cA
    elnpi
    @0
    @1
    @2
    @5
    simpl3
    sylbi
end
