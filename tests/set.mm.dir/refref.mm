include "wcel.mm"
include "cref.mm"
include "wbr.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "isref.mm"
include "mpbiri.mm"

theorem refref
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> A Ref A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cref
    wbr
    cA
    cuni
    #
    @0
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wral
    #
    wa
    @1
    @6
    @0
    eqid
    #
    @5
    vx
    cA
    @2
    cA
    wcel
    @2
    @2
    wss
    #
    @5
    @2
    ssid
    @4
    @8
    vy
    @2
    cA
    @3
    @2
    @2
    sseq2
    rspcev
    mpan2
    rgen
    pm3.2i
    vx
    vy
    cA
    cA
    cV
    @0
    @0
    @7
    @7
    isref
    mpbiri
end
