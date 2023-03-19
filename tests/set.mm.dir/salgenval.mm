include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "csalg.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "csalgen.mm"
include "cmpt.mm"
include "df-salgen.mm"
include "a1i.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "adantl.mm"
include "elex.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "uniexg.mm"
include "pwsal.mm"
include "syl.mm"
include "unipw.mm"
include "pwuni.mm"
include "jca32.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "intex.mm"
include "sylib.mm"
include "fvmptd.mm"

theorem salgenval
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k

  disjoint X s
  disjoint V x
  disjoint X x
  disjoint s x
  disjoint k x
  assert |- ( X e. V -> ( SalGen ` X ) = |^| { s e. SAlg | ( U. s = U. X /\ X C_ s ) } )

  proof
    cX
    cV
    wcel
    #
    vx
    cX
    vs
    cv
    #
    cuni
    #
    vx
    cv
    #
    cuni
    #
    wceq
    #
    @3
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
    @2
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
    cvv
    csalgen
    cvv
    csalgen
    vx
    cvv
    @9
    cmpt
    wceq
    @0
    vx
    vs
    df-salgen
    a1i
    @3
    cX
    wceq
    #
    @9
    @15
    wceq
    @0
    @16
    @8
    @14
    @16
    @7
    @13
    vs
    csalg
    @16
    @5
    @11
    @6
    @12
    @16
    @4
    @10
    @2
    @3
    cX
    unieq
    eqeq2d
    @3
    cX
    @1
    sseq1
    anbi12d
    rabbidv
    inteqd
    adantl
    cX
    cV
    elex
    @0
    @14
    c0
    wne
    #
    @15
    cvv
    wcel
    @0
    @10
    cpw
    #
    @14
    wcel
    #
    @17
    @0
    @18
    csalg
    wcel
    #
    @18
    cuni
    #
    @10
    wceq
    #
    cX
    @18
    wss
    #
    wa
    #
    wa
    @19
    @0
    @20
    @22
    @23
    @0
    @10
    cvv
    wcel
    @20
    cX
    cV
    uniexg
    cvv
    @10
    pwsal
    syl
    @22
    @0
    @10
    unipw
    a1i
    @23
    @0
    cX
    pwuni
    a1i
    jca32
    @13
    @24
    vs
    @18
    csalg
    @1
    @18
    wceq
    #
    @11
    @22
    @12
    @23
    @25
    @2
    @21
    @10
    @1
    @18
    unieq
    eqeq1d
    @1
    @18
    cX
    sseq2
    anbi12d
    elrab
    sylibr
    @14
    @18
    ne0i
    syl
    @14
    intex
    sylib
    fvmptd
end
