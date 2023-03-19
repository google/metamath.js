include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "csiga.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "csigagen.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-sigagen.mm"
include "a1i.mm"
include "unieq.mm"
include "fveq2d.mm"
include "sseq1.mm"
include "rabeqbidv.mm"
include "inteqd.mm"
include "adantl.mm"
include "elex.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "wa.mm"
include "uniexg.mm"
include "pwsiga.mm"
include "syl.mm"
include "pwuni.mm"
include "jctir.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "intex.mm"
include "sylib.mm"
include "fvmptd.mm"

theorem sigagenval
  let cA: class A
  let cV: class V
  let vs: setvar s
  let vx: setvar x

  disjoint A s
  disjoint s x
  disjoint A x
  disjoint V x
  assert |- ( A e. V -> ( sigaGen ` A ) = |^| { s e. ( sigAlgebra ` U. A ) | A C_ s } )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vx
    cv
    #
    vs
    cv
    #
    wss
    #
    vs
    @1
    cuni
    #
    csiga
    cfv
    #
    crab
    #
    cint
    #
    cA
    @2
    wss
    #
    vs
    cA
    cuni
    #
    csiga
    cfv
    #
    crab
    #
    cint
    #
    cvv
    csigagen
    cvv
    csigagen
    vx
    cvv
    @7
    cmpt
    wceq
    @0
    vx
    vs
    df-sigagen
    a1i
    @1
    cA
    wceq
    #
    @7
    @12
    wceq
    @0
    @13
    @6
    @11
    @13
    @3
    @8
    vs
    @5
    @10
    @13
    @4
    @9
    csiga
    @1
    cA
    unieq
    fveq2d
    @1
    cA
    @2
    sseq1
    rabeqbidv
    inteqd
    adantl
    cA
    cV
    elex
    @0
    @11
    c0
    wne
    #
    @12
    cvv
    wcel
    @0
    @9
    cpw
    #
    @11
    wcel
    #
    @14
    @0
    @15
    @10
    wcel
    #
    cA
    @15
    wss
    #
    wa
    @16
    @0
    @17
    @18
    @0
    @9
    cvv
    wcel
    @17
    cA
    cV
    uniexg
    @9
    cvv
    pwsiga
    syl
    cA
    pwuni
    jctir
    @8
    @18
    vs
    @15
    @10
    @2
    @15
    cA
    sseq2
    elrab
    sylibr
    @11
    @15
    ne0i
    syl
    @11
    intex
    sylib
    fvmptd
end
