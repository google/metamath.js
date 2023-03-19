include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "csalg.mm"
include "crab.mm"
include "cint.mm"
include "ssint.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "biimpi.mm"
include "simprrd.mm"
include "mprgbir.mm"
include "a1i.mm"
include "csalgen.mm"
include "cfv.mm"
include "salgenval.mm"
include "syl5req.mm"
include "sseqtrd.mm"

theorem sssalgen
  let cS: class S
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vx: setvar x
  assume sssalgen.1: |- S = ( SalGen ` X )


  assert |- ( X e. V -> X C_ S )

  proof
    cX
    cV
    wcel
    #
    cX
    vs
    cv
    #
    cuni
    #
    cX
    cuni
    #
    wceq
    #
    cX
    @1
    wss
    #
    wa
    #
    vs
    csalg
    crab
    #
    cint
    #
    cS
    cX
    @8
    wss
    #
    @0
    @9
    cX
    vt
    cv
    #
    wss
    #
    vt
    @7
    vt
    cX
    @7
    ssint
    @10
    @7
    wcel
    #
    @10
    csalg
    wcel
    #
    @10
    cuni
    #
    @3
    wceq
    #
    @11
    @12
    @13
    @15
    @11
    wa
    #
    wa
    @6
    @16
    vs
    @10
    csalg
    @1
    @10
    wceq
    #
    @4
    @15
    @5
    @11
    @17
    @2
    @14
    @3
    @1
    @10
    unieq
    eqeq1d
    @1
    @10
    cX
    sseq2
    anbi12d
    elrab
    biimpi
    simprrd
    mprgbir
    a1i
    @0
    cS
    cX
    csalgen
    cfv
    @8
    sssalgen.1
    cV
    cX
    vs
    salgenval
    syl5req
    sseqtrd
end
