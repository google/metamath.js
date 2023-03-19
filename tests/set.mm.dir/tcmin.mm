include "wcel.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "cv.mm"
include "cab.mm"
include "cint.mm"
include "ctc.mm"
include "cfv.mm"
include "wex.mm"
include "cvv.mm"
include "tcvalg.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "intexab.mm"
include "sylibr.mm"
include "cin.mm"
include "ssin.mm"
include "biimpi.mm"
include "trin.mm"
include "anim12i.mm"
include "an4s.mm"
include "expcom.mm"
include "vex.mm"
include "inex1.mm"
include "wceq.mm"
include "sseq2.mm"
include "treq.mm"
include "anbi12d.mm"
include "elab.mm"
include "intss1.mm"
include "sylbir.mm"
include "inss2.mm"
include "syl6ss.mm"
include "syl6.mm"
include "exlimdv.mm"
include "syl5com.mm"
include "sseq1d.mm"
include "sylibrd.mm"

theorem tcmin
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( ( A C_ B /\ Tr B ) -> ( TC ` A ) C_ B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    wss
    #
    cB
    wtr
    #
    wa
    #
    cA
    vy
    cv
    #
    wss
    #
    @4
    wtr
    #
    wa
    #
    vy
    cab
    #
    cint
    #
    cB
    wss
    #
    cA
    ctc
    cfv
    #
    cB
    wss
    @0
    cA
    vx
    cv
    #
    wss
    #
    @12
    wtr
    #
    wa
    #
    vx
    wex
    #
    @3
    @10
    @0
    @15
    vx
    cab
    cint
    #
    cvv
    wcel
    @16
    @0
    @17
    @11
    cvv
    vx
    cA
    cV
    tcvalg
    cA
    ctc
    fvex
    syl6eqelr
    @15
    vx
    intexab
    sylibr
    @3
    @15
    @10
    vx
    @3
    @15
    cA
    @12
    cB
    cin
    #
    wss
    #
    @18
    wtr
    #
    wa
    #
    @10
    @15
    @3
    @21
    @13
    @1
    @14
    @2
    @21
    @13
    @1
    wa
    #
    @19
    @14
    @2
    wa
    @20
    @22
    @19
    cA
    @12
    cB
    ssin
    biimpi
    @12
    cB
    trin
    anim12i
    an4s
    expcom
    @21
    @9
    @18
    cB
    @21
    @18
    @8
    wcel
    @9
    @18
    wss
    @7
    @21
    vy
    @18
    @12
    cB
    vx
    vex
    inex1
    @4
    @18
    wceq
    @5
    @19
    @6
    @20
    @4
    @18
    cA
    sseq2
    @4
    @18
    treq
    anbi12d
    elab
    @18
    @8
    intss1
    sylbir
    @12
    cB
    inss2
    syl6ss
    syl6
    exlimdv
    syl5com
    @0
    @11
    @9
    cB
    vy
    cA
    cV
    tcvalg
    sseq1d
    sylibrd
end
