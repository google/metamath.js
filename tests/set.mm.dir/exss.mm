include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wex.mm"
include "wss.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "df-rab.mm"
include "neeq1i.mm"
include "rabn0.mm"
include "n0.mm"
include "3bitr3i.mm"
include "csn.mm"
include "vex.mm"
include "snss.mm"
include "ssab2.mm"
include "sstr2.mm"
include "mpi.mm"
include "sylbi.mm"
include "wsb.mm"
include "simpr.mm"
include "wceq.mm"
include "equsb1.mm"
include "velsn.mm"
include "sbbii.mm"
include "mpbir.mm"
include "jctil.mm"
include "df-clab.mm"
include "sban.mm"
include "bitri.mm"
include "eleq2i.mm"
include "3imtr4i.mm"
include "ne0i.mm"
include "syl.mm"
include "sylib.mm"
include "snex.mm"
include "sseq1.mm"
include "rexeq.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "exlimiv.mm"

theorem exss
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  assert |- ( E. x e. A ph -> E. y ( y C_ A /\ E. x e. y ph ) )

  proof
    wph
    vx
    cA
    wrex
    #
    vz
    cv
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    wcel
    #
    vz
    wex
    #
    vy
    cv
    #
    cA
    wss
    #
    wph
    vx
    @8
    wrex
    #
    wa
    #
    vy
    wex
    #
    wph
    vx
    cA
    crab
    #
    c0
    wne
    @5
    c0
    wne
    @0
    @7
    @13
    @5
    c0
    wph
    vx
    cA
    df-rab
    neeq1i
    wph
    vx
    cA
    rabn0
    vz
    @5
    n0
    3bitr3i
    @6
    @12
    vz
    @6
    @1
    csn
    #
    cA
    wss
    #
    wph
    vx
    @14
    wrex
    #
    @12
    @6
    @14
    @5
    wss
    #
    @15
    @1
    @5
    vz
    vex
    snss
    @17
    @5
    cA
    wss
    @15
    wph
    vx
    cA
    ssab2
    @14
    @5
    cA
    sstr2
    mpi
    sylbi
    @6
    wph
    vx
    @14
    crab
    #
    c0
    wne
    #
    @16
    @6
    @1
    @18
    wcel
    #
    @19
    @3
    vx
    vz
    wsb
    #
    wph
    vx
    vz
    wsb
    #
    wa
    #
    @2
    @14
    wcel
    #
    vx
    vz
    wsb
    #
    @22
    wa
    #
    @6
    @20
    @23
    @22
    @25
    @21
    @22
    simpr
    @25
    @2
    @1
    wceq
    #
    vx
    vz
    wsb
    vx
    vz
    equsb1
    @24
    @27
    vx
    vz
    vx
    @1
    velsn
    sbbii
    mpbir
    jctil
    @6
    @4
    vx
    vz
    wsb
    @23
    @4
    vz
    vx
    df-clab
    @3
    wph
    vx
    vz
    sban
    bitri
    @20
    @1
    @24
    wph
    wa
    #
    vx
    cab
    #
    wcel
    #
    @26
    @18
    @29
    @1
    wph
    vx
    @14
    df-rab
    eleq2i
    @30
    @28
    vx
    vz
    wsb
    @26
    @28
    vz
    vx
    df-clab
    @24
    wph
    vx
    vz
    sban
    bitri
    bitri
    3imtr4i
    @18
    @1
    ne0i
    syl
    wph
    vx
    @14
    rabn0
    sylib
    @11
    @15
    @16
    wa
    vy
    @14
    @1
    snex
    @8
    @14
    wceq
    @9
    @15
    @10
    @16
    @8
    @14
    cA
    sseq1
    wph
    vx
    @8
    @14
    rexeq
    anbi12d
    spcev
    syl2anc
    exlimiv
    sylbi
end
