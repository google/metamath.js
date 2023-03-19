include "wcel.mm"
include "cuni.mm"
include "cpw.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "csalg.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "uniexg.mm"
include "pwsal.mm"
include "syl.mm"
include "unipw.mm"
include "a1i.mm"
include "pwuni.mm"
include "jca.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"

theorem salgenn0
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x

  disjoint X s
  disjoint k x
  assert |- ( X e. V -> { s e. SAlg | ( U. s = U. X /\ X C_ s ) } =/= (/) )

  proof
    cX
    cV
    wcel
    #
    cX
    cuni
    #
    cpw
    #
    vs
    cv
    #
    cuni
    #
    @1
    wceq
    #
    cX
    @3
    wss
    #
    wa
    #
    vs
    csalg
    crab
    #
    wcel
    #
    @8
    c0
    wne
    @0
    @2
    csalg
    wcel
    #
    @2
    cuni
    #
    @1
    wceq
    #
    cX
    @2
    wss
    #
    wa
    #
    wa
    @9
    @0
    @10
    @14
    @0
    @1
    cvv
    wcel
    @10
    cX
    cV
    uniexg
    cvv
    @1
    pwsal
    syl
    @0
    @12
    @13
    @12
    @0
    @1
    unipw
    a1i
    @13
    @0
    cX
    pwuni
    a1i
    jca
    jca
    @7
    @14
    vs
    @2
    csalg
    @3
    @2
    wceq
    #
    @5
    @12
    @6
    @13
    @15
    @4
    @11
    @1
    @3
    @2
    unieq
    eqeq1d
    @3
    @2
    cX
    sseq2
    anbi12d
    elrab
    sylibr
    @8
    @2
    ne0i
    syl
end
