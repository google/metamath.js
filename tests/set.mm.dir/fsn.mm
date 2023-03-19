include "csn.mm"
include "wf.mm"
include "cop.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "opelf.mm"
include "velsn.mm"
include "anbi12i.mm"
include "sylib.mm"
include "ex.mm"
include "wreu.mm"
include "snid.mm"
include "feu.mm"
include "mpan2.mm"
include "weu.mm"
include "anbi1i.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "pm5.32i.mm"
include "ancom.mm"
include "bitr4i.mm"
include "bitr2i.mm"
include "eubii.mm"
include "eueq1.mm"
include "biantru.mm"
include "euanv.mm"
include "df-reu.mm"
include "3bitr4i.mm"
include "sylibr.mm"
include "opeq12.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "opex.mm"
include "elsn.mm"
include "opth2.mm"
include "syl6bb.mm"
include "alrimivv.mm"
include "wrel.mm"
include "frel.mm"
include "relsnop.mm"
include "eqrel.mm"
include "sylancl.mm"
include "mpbird.mm"
include "wf1o.mm"
include "f1osn.mm"
include "f1oeq1.mm"
include "mpbiri.mm"
include "f1of.mm"
include "syl.mm"
include "impbii.mm"

theorem fsn
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume fsn.1: |- A e. _V
  assume fsn.2: |- B e. _V


  assert |- ( F : { A } --> { B } <-> F = { <. A , B >. } )

  proof
    cA
    csn
    #
    cB
    csn
    #
    cF
    wf
    #
    cF
    cA
    cB
    cop
    #
    csn
    #
    wceq
    #
    @2
    @5
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cF
    wcel
    #
    @8
    @4
    wcel
    #
    wb
    #
    vy
    wal
    vx
    wal
    #
    @2
    @11
    vx
    vy
    @2
    @9
    @6
    cA
    wceq
    #
    @7
    cB
    wceq
    #
    wa
    #
    @10
    @2
    @9
    @15
    @2
    @9
    @15
    @2
    @9
    wa
    @6
    @0
    wcel
    #
    @7
    @1
    wcel
    #
    wa
    @15
    @0
    @1
    @6
    @7
    cF
    opelf
    @16
    @13
    @17
    @14
    vx
    cA
    velsn
    vy
    cB
    velsn
    #
    anbi12i
    sylib
    ex
    @2
    @9
    @15
    @3
    cF
    wcel
    #
    @2
    cA
    @7
    cop
    #
    cF
    wcel
    #
    vy
    @1
    wreu
    #
    @19
    @2
    cA
    @0
    wcel
    @22
    cA
    fsn.1
    snid
    vy
    @0
    @1
    cA
    cF
    feu
    mpan2
    @19
    @14
    wa
    #
    vy
    weu
    #
    @17
    @21
    wa
    #
    vy
    weu
    @19
    @22
    @23
    @25
    vy
    @25
    @14
    @21
    wa
    #
    @23
    @17
    @14
    @21
    @18
    anbi1i
    @26
    @14
    @19
    wa
    @23
    @14
    @21
    @19
    @14
    @20
    @3
    cF
    @7
    cB
    cA
    opeq2
    eleq1d
    pm5.32i
    @19
    @14
    ancom
    bitr4i
    bitr2i
    eubii
    @19
    @19
    @14
    vy
    weu
    #
    wa
    @24
    @27
    @19
    vy
    cB
    fsn.2
    eueq1
    biantru
    @19
    @14
    vy
    euanv
    bitr4i
    @21
    vy
    @1
    df-reu
    3bitr4i
    sylibr
    @15
    @8
    @3
    cF
    @6
    @7
    cA
    cB
    opeq12
    eleq1d
    syl5ibrcom
    impbid
    @10
    @8
    @3
    wceq
    @15
    @8
    @3
    @6
    @7
    opex
    elsn
    @6
    @7
    cA
    cB
    fsn.1
    fsn.2
    opth2
    bitr2i
    syl6bb
    alrimivv
    @2
    cF
    wrel
    @4
    wrel
    @5
    @12
    wb
    @0
    @1
    cF
    frel
    cA
    cB
    fsn.1
    fsn.2
    relsnop
    vx
    vy
    cF
    @4
    eqrel
    sylancl
    mpbird
    @5
    @0
    @1
    cF
    wf1o
    #
    @2
    @5
    @28
    @0
    @1
    @4
    wf1o
    cA
    cB
    fsn.1
    fsn.2
    f1osn
    @0
    @1
    cF
    @4
    f1oeq1
    mpbiri
    @0
    @1
    cF
    f1of
    syl
    impbii
end
