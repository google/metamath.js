include "wcel.mm"
include "cfne.mm"
include "wbr.mm"
include "cuni.mm"
include "wceq.mm"
include "wel.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "ssid.mm"
include "elequ2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "rgen2.mm"
include "pm3.2i.mm"
include "isfne2.mm"
include "mpbiri.mm"

theorem fneref
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> A Fne A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cfne
    wbr
    cA
    cuni
    #
    @0
    wceq
    #
    vy
    vz
    wel
    #
    vz
    cv
    #
    vx
    cv
    #
    wss
    #
    wa
    #
    vz
    cA
    wrex
    #
    vy
    @4
    wral
    vx
    cA
    wral
    #
    wa
    @1
    @8
    @0
    eqid
    #
    @7
    vx
    vy
    cA
    @4
    @4
    cA
    wcel
    vy
    vx
    wel
    #
    @4
    @4
    wss
    #
    @7
    @4
    ssid
    @6
    @10
    @11
    wa
    vz
    @4
    cA
    @3
    @4
    wceq
    @2
    @10
    @5
    @11
    vz
    vx
    vy
    elequ2
    @3
    @4
    @4
    sseq1
    anbi12d
    rspcev
    mpanr2
    rgen2
    pm3.2i
    vx
    vy
    vz
    cA
    cA
    cV
    @0
    @0
    @9
    @9
    isfne2
    mpbiri
end
