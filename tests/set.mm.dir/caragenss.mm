include "come.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "a1i.mm"
include "ccaragen.mm"
include "caragenval.mm"
include "eqtrd.mm"
include "omedm.mm"
include "sseq12d.mm"
include "mpbird.mm"

theorem caragenss
  let cS: class S
  let cO: class O
  let va: setvar a
  let ve: setvar e
  let vk: setvar k
  let vx: setvar x
  assume caragenss.1: |- S = ( CaraGen ` O )


  assert |- ( O e. OutMeas -> S C_ dom O )

  proof
    cO
    come
    wcel
    #
    cS
    cO
    cdm
    #
    wss
    va
    cv
    #
    ve
    cv
    #
    cin
    cO
    cfv
    @2
    @3
    cdif
    cO
    cfv
    cxad
    co
    @2
    cO
    cfv
    wceq
    va
    @1
    cuni
    cpw
    #
    wral
    #
    ve
    @4
    crab
    #
    @4
    wss
    #
    @7
    @0
    @5
    ve
    @4
    ssrab2
    a1i
    @0
    cS
    @6
    @1
    @4
    @0
    cS
    cO
    ccaragen
    cfv
    #
    @6
    cS
    @8
    wceq
    @0
    caragenss.1
    a1i
    ve
    cO
    va
    caragenval
    eqtrd
    cO
    omedm
    sseq12d
    mpbird
end
