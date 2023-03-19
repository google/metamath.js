include "wcel.mm"
include "csalgen.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "csalg.mm"
include "crab.mm"
include "cint.mm"
include "salgenval.mm"
include "ssrab2.mm"
include "a1i.mm"
include "salgenn0.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "biimpi.mm"
include "simprld.mm"
include "adantl.mm"
include "intsal.mm"
include "eqeltrd.mm"

theorem salgencl
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x


  assert |- ( X e. V -> ( SalGen ` X ) e. SAlg )

  proof
    cX
    cV
    wcel
    #
    cX
    csalgen
    cfv
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
    csalg
    cV
    cX
    vs
    salgenval
    @0
    @7
    @3
    vt
    @7
    csalg
    wss
    @0
    @6
    vs
    csalg
    ssrab2
    a1i
    cV
    cX
    vs
    salgenn0
    vt
    cv
    #
    @7
    wcel
    #
    @8
    cuni
    #
    @3
    wceq
    #
    @0
    @9
    @8
    csalg
    wcel
    #
    @11
    cX
    @8
    wss
    #
    @9
    @12
    @11
    @13
    wa
    #
    wa
    @6
    @14
    vs
    @8
    csalg
    @1
    @8
    wceq
    #
    @4
    @11
    @5
    @13
    @15
    @2
    @10
    @3
    @1
    @8
    unieq
    eqeq1d
    @1
    @8
    cX
    sseq2
    anbi12d
    elrab
    biimpi
    simprld
    adantl
    intsal
    eqeltrd
end
