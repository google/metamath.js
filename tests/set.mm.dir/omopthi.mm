include "coa.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wcel.mm"
include "wo.mm"
include "word.mm"
include "wb.mm"
include "nnacli.mm"
include "nnoni.mm"
include "onordi.mm"
include "ordtri3.mm"
include "mp2an.mm"
include "con2bii.mm"
include "omopthlem2.mm"
include "eqcom.mm"
include "sylnib.mm"
include "jaoi.mm"
include "sylbir.mm"
include "con4i.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "com.mm"
include "nnmcli.mm"
include "nnacan.mm"
include "mp3an.mm"
include "sylib.mm"
include "oveq2d.mm"
include "nnacom.mm"
include "3eqtr4g.mm"
include "jca.mm"
include "oveq12.mm"
include "simpr.mm"
include "impbii.mm"

theorem omopthi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume omopth.1: |- A e. _om
  assume omopth.2: |- B e. _om
  assume omopth.3: |- C e. _om
  assume omopth.4: |- D e. _om


  assert |- ( ( ( ( A +o B ) .o ( A +o B ) ) +o B ) = ( ( ( C +o D ) .o ( C +o D ) ) +o D ) <-> ( A = C /\ B = D ) )

  proof
    cA
    cB
    coa
    co
    #
    @0
    comu
    co
    #
    cB
    coa
    co
    #
    cC
    cD
    coa
    co
    #
    @3
    comu
    co
    #
    cD
    coa
    co
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    @6
    @7
    @8
    @6
    cB
    cA
    coa
    co
    #
    cB
    cC
    coa
    co
    #
    wceq
    #
    @7
    @6
    @0
    cC
    cB
    coa
    co
    #
    @10
    @11
    @6
    @0
    @3
    @13
    @0
    @3
    wceq
    #
    @6
    @14
    wn
    @0
    @3
    wcel
    #
    @3
    @0
    wcel
    #
    wo
    #
    @6
    wn
    #
    @14
    @17
    @0
    word
    @3
    word
    @14
    @17
    wn
    wb
    @0
    @0
    cA
    cB
    omopth.1
    omopth.2
    nnacli
    #
    nnoni
    onordi
    @3
    @3
    cC
    cD
    omopth.3
    omopth.4
    nnacli
    #
    nnoni
    onordi
    @0
    @3
    ordtri3
    mp2an
    con2bii
    @15
    @18
    @16
    @15
    @5
    @2
    wceq
    @6
    cA
    cB
    @3
    cD
    omopth.1
    omopth.2
    @20
    omopth.4
    omopthlem2
    @5
    @2
    eqcom
    sylnib
    cC
    cD
    @0
    cB
    omopth.3
    omopth.4
    @19
    omopth.2
    omopthlem2
    jaoi
    sylbir
    con4i
    #
    @6
    cB
    cD
    cC
    coa
    @6
    @2
    @1
    cD
    coa
    co
    #
    wceq
    #
    @8
    @6
    @2
    @5
    @22
    @6
    id
    @6
    @1
    @4
    cD
    coa
    @6
    @0
    @3
    @0
    @3
    comu
    @21
    @21
    oveq12d
    oveq1d
    eqtr4d
    @1
    com
    wcel
    cB
    com
    wcel
    #
    cD
    com
    wcel
    @23
    @8
    wb
    @0
    @0
    @19
    @19
    nnmcli
    omopth.2
    omopth.4
    @1
    cB
    cD
    nnacan
    mp3an
    sylib
    #
    oveq2d
    eqtr4d
    @24
    cA
    com
    wcel
    #
    @10
    @0
    wceq
    omopth.2
    omopth.1
    cB
    cA
    nnacom
    mp2an
    @24
    cC
    com
    wcel
    #
    @11
    @13
    wceq
    omopth.2
    omopth.3
    cB
    cC
    nnacom
    mp2an
    3eqtr4g
    @24
    @26
    @27
    @12
    @7
    wb
    omopth.2
    omopth.1
    omopth.3
    cB
    cA
    cC
    nnacan
    mp3an
    sylib
    @25
    jca
    @9
    @1
    @4
    cB
    cD
    coa
    @9
    @0
    @3
    @0
    @3
    comu
    cA
    cC
    cB
    cD
    coa
    oveq12
    #
    @28
    oveq12d
    @7
    @8
    simpr
    oveq12d
    impbii
end
