include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cif.mm"
include "wceq.mm"
include "biidd.mm"
include "eleq2.mm"
include "eleq1.mm"
include "wss.mm"
include "sseq1.mm"
include "sseq2.mm"
include "ssid.mm"
include "keephyp3v.mm"
include "0ex.mm"
include "snid.mm"
include "elimhyp3v.mm"
include "sselii.mm"
include "dedth3v.mm"

theorem sseliALT
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseliALT.1: |- A C_ B


  assert |- ( C e. A -> C e. B )

  proof
    cC
    cA
    wcel
    #
    cC
    cB
    wcel
    #
    @1
    cC
    @0
    cB
    c0
    csn
    #
    cif
    #
    wcel
    @0
    cC
    c0
    cif
    #
    @3
    wcel
    cA
    cB
    cC
    @2
    @2
    c0
    cA
    @0
    cA
    @2
    cif
    #
    wceq
    @1
    biidd
    cB
    @3
    cC
    eleq2
    cC
    @4
    @3
    eleq1
    @5
    @3
    @4
    @0
    @5
    cB
    wss
    @5
    @3
    wss
    #
    @6
    @2
    @2
    wss
    @5
    @2
    wss
    @6
    cA
    cB
    wss
    cA
    cB
    cC
    @2
    @2
    c0
    cA
    @5
    cB
    sseq1
    cB
    @3
    @5
    sseq2
    cC
    @4
    wceq
    @6
    biidd
    @2
    @5
    @2
    sseq1
    @2
    @3
    @5
    sseq2
    c0
    @4
    wceq
    @6
    biidd
    sseliALT.1
    @2
    ssid
    keephyp3v
    @0
    cC
    @5
    wcel
    #
    @7
    @4
    @5
    wcel
    c0
    @2
    wcel
    c0
    @5
    wcel
    #
    @8
    cA
    cB
    cC
    @2
    @2
    c0
    cA
    @5
    cC
    eleq2
    cB
    @3
    wceq
    @7
    biidd
    cC
    @4
    @5
    eleq1
    @2
    @5
    c0
    eleq2
    @2
    @3
    wceq
    @8
    biidd
    c0
    @4
    @5
    eleq1
    c0
    0ex
    snid
    elimhyp3v
    sselii
    dedth3v
end
