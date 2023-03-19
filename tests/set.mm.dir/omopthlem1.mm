include "csuc.mm"
include "wss.mm"
include "comu.mm"
include "co.mm"
include "wcel.mm"
include "c2o.mm"
include "coa.mm"
include "com.mm"
include "wi.mm"
include "peano2.mm"
include "ax-mp.mm"
include "nnmwordi.mm"
include "mp3an.mm"
include "nnmwordri.mm"
include "sstrd.mm"
include "nnoni.mm"
include "onsucssi.mm"
include "nnmcli.mm"
include "2onn.mm"
include "nnacli.mm"
include "wceq.mm"
include "nnasuc.mm"
include "mp2an.mm"
include "nnmsuc.mm"
include "nnaass.mm"
include "nnmcom.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "nnm2.mm"
include "oveq2i.mm"
include "3eqtr4ri.mm"
include "suceq.mm"
include "sseq1i.mm"
include "bitri.mm"
include "3imtr4i.mm"

theorem omopthlem1
  let cA: class A
  let cC: class C
  assume omopthlem1.1: |- A e. _om
  assume omopthlem1.2: |- C e. _om


  assert |- ( A e. C -> ( ( A .o A ) +o ( A .o 2o ) ) e. ( C .o C ) )

  proof
    cA
    csuc
    #
    cC
    wss
    #
    @0
    @0
    comu
    co
    #
    cC
    cC
    comu
    co
    #
    wss
    #
    cA
    cC
    wcel
    cA
    cA
    comu
    co
    #
    cA
    c2o
    comu
    co
    #
    coa
    co
    #
    @3
    wcel
    #
    @1
    @2
    @0
    cC
    comu
    co
    #
    @3
    @0
    com
    wcel
    #
    cC
    com
    wcel
    #
    @10
    @1
    @2
    @9
    wss
    wi
    cA
    com
    wcel
    #
    @10
    omopthlem1.1
    cA
    peano2
    ax-mp
    #
    omopthlem1.2
    @13
    @0
    cC
    @0
    nnmwordi
    mp3an
    @10
    @11
    @11
    @1
    @9
    @3
    wss
    wi
    @13
    omopthlem1.2
    omopthlem1.2
    @0
    cC
    cC
    nnmwordri
    mp3an
    sstrd
    cA
    cC
    cA
    omopthlem1.1
    nnoni
    cC
    omopthlem1.2
    nnoni
    onsucssi
    @8
    @7
    csuc
    #
    @3
    wss
    @4
    @7
    @3
    @7
    @5
    @6
    cA
    cA
    omopthlem1.1
    omopthlem1.1
    nnmcli
    #
    cA
    c2o
    omopthlem1.1
    2onn
    nnmcli
    nnacli
    nnoni
    @3
    cC
    cC
    omopthlem1.2
    omopthlem1.2
    nnmcli
    nnoni
    onsucssi
    @14
    @2
    @3
    @0
    cA
    comu
    co
    #
    @0
    coa
    co
    #
    @16
    cA
    coa
    co
    #
    csuc
    #
    @2
    @14
    @16
    com
    wcel
    @12
    @17
    @19
    wceq
    @0
    cA
    @13
    omopthlem1.1
    nnmcli
    omopthlem1.1
    @16
    cA
    nnasuc
    mp2an
    @10
    @12
    @2
    @17
    wceq
    @13
    omopthlem1.1
    @0
    cA
    nnmsuc
    mp2an
    @7
    @18
    wceq
    @14
    @19
    wceq
    @5
    cA
    coa
    co
    #
    cA
    coa
    co
    #
    @5
    cA
    cA
    coa
    co
    #
    coa
    co
    #
    @18
    @7
    @5
    com
    wcel
    @12
    @12
    @21
    @23
    wceq
    @15
    omopthlem1.1
    omopthlem1.1
    @5
    cA
    cA
    nnaass
    mp3an
    @16
    @20
    cA
    coa
    @16
    cA
    @0
    comu
    co
    #
    @20
    @10
    @12
    @16
    @24
    wceq
    @13
    omopthlem1.1
    @0
    cA
    nnmcom
    mp2an
    @12
    @12
    @24
    @20
    wceq
    omopthlem1.1
    omopthlem1.1
    cA
    cA
    nnmsuc
    mp2an
    eqtri
    oveq1i
    @6
    @22
    @5
    coa
    @12
    @6
    @22
    wceq
    omopthlem1.1
    cA
    nnm2
    ax-mp
    oveq2i
    3eqtr4ri
    @7
    @18
    suceq
    ax-mp
    3eqtr4ri
    sseq1i
    bitri
    3imtr4i
end
