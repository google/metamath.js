include "comu.mm"
include "co.mm"
include "coa.mm"
include "wceq.mm"
include "wcel.mm"
include "nnmcli.mm"
include "nnacli.mm"
include "nnoni.mm"
include "onirri.mm"
include "eleq1.mm"
include "mtbii.mm"
include "com.mm"
include "wss.mm"
include "nnaword1.mm"
include "mp2an.mm"
include "c2o.mm"
include "nnacom.mm"
include "sseqtri.mm"
include "nnaass.mm"
include "mp3an.mm"
include "nnm2.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "wi.mm"
include "2onn.mm"
include "nnawordi.mm"
include "3sstr4i.mm"
include "omopthlem1.mm"
include "con0.mm"
include "wa.mm"
include "ontr2.mm"
include "sylancr.mm"
include "sseldi.mm"
include "nsyl3.mm"

theorem omopthlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume omopthlem2.1: |- A e. _om
  assume omopthlem2.2: |- B e. _om
  assume omopthlem2.3: |- C e. _om
  assume omopthlem2.4: |- D e. _om


  assert |- ( ( A +o B ) e. C -> -. ( ( C .o C ) +o D ) = ( ( ( A +o B ) .o ( A +o B ) ) +o B ) )

  proof
    cC
    cC
    comu
    co
    #
    cD
    coa
    co
    #
    cA
    cB
    coa
    co
    #
    @2
    comu
    co
    #
    cB
    coa
    co
    #
    wceq
    #
    @4
    @1
    wcel
    #
    @2
    cC
    wcel
    #
    @5
    @1
    @1
    wcel
    @6
    @1
    @1
    @0
    cD
    cC
    cC
    omopthlem2.3
    omopthlem2.3
    nnmcli
    #
    omopthlem2.4
    nnacli
    nnoni
    onirri
    @1
    @4
    @1
    eleq1
    mtbii
    @7
    @0
    @1
    @4
    @0
    com
    wcel
    cD
    com
    wcel
    @0
    @1
    wss
    @8
    omopthlem2.4
    @0
    cD
    nnaword1
    mp2an
    @7
    @4
    @3
    @2
    c2o
    comu
    co
    #
    coa
    co
    #
    wss
    #
    @10
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    cB
    @3
    coa
    co
    #
    @9
    @3
    coa
    co
    #
    @4
    @10
    cB
    @9
    wss
    #
    @14
    @15
    wss
    #
    cB
    @2
    cA
    coa
    co
    #
    cB
    coa
    co
    #
    @9
    cB
    cB
    @18
    coa
    co
    #
    @19
    cB
    com
    wcel
    #
    @18
    com
    wcel
    #
    cB
    @20
    wss
    omopthlem2.2
    @2
    cA
    cA
    cB
    omopthlem2.1
    omopthlem2.2
    nnacli
    #
    omopthlem2.1
    nnacli
    #
    cB
    @18
    nnaword1
    mp2an
    @21
    @22
    @20
    @19
    wceq
    omopthlem2.2
    @24
    cB
    @18
    nnacom
    mp2an
    sseqtri
    @19
    @2
    @2
    coa
    co
    #
    @9
    @2
    com
    wcel
    #
    cA
    com
    wcel
    @21
    @19
    @25
    wceq
    @23
    omopthlem2.1
    omopthlem2.2
    @2
    cA
    cB
    nnaass
    mp3an
    @26
    @9
    @25
    wceq
    @23
    @2
    nnm2
    ax-mp
    eqtr4i
    sseqtri
    @21
    @9
    com
    wcel
    #
    @3
    com
    wcel
    #
    @16
    @17
    wi
    omopthlem2.2
    @2
    c2o
    @23
    2onn
    nnmcli
    #
    @2
    @2
    @23
    @23
    nnmcli
    #
    cB
    @9
    @3
    nnawordi
    mp3an
    ax-mp
    @28
    @21
    @4
    @14
    wceq
    @30
    omopthlem2.2
    @3
    cB
    nnacom
    mp2an
    @28
    @27
    @10
    @15
    wceq
    @30
    @29
    @3
    @9
    nnacom
    mp2an
    3sstr4i
    @2
    cC
    @23
    omopthlem2.3
    omopthlem1
    @4
    con0
    wcel
    @0
    con0
    wcel
    @11
    @12
    wa
    @13
    wi
    @4
    @3
    cB
    @30
    omopthlem2.2
    nnacli
    nnoni
    @0
    @8
    nnoni
    @4
    @10
    @0
    ontr2
    mp2an
    sylancr
    sseldi
    nsyl3
end
