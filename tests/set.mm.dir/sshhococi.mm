include "chj.mm"
include "co.mm"
include "cort.mm"
include "cfv.mm"
include "cun.mm"
include "wss.mm"
include "chil.mm"
include "ococss.mm"
include "ax-mp.mm"
include "unss12.mm"
include "mp2an.mm"
include "unssi.mm"
include "cch.mm"
include "wcel.mm"
include "occl.mm"
include "choccli.mm"
include "chssii.mm"
include "occon2i.mm"
include "wceq.mm"
include "sshjval.mm"
include "chjvali.mm"
include "3sstr4i.mm"
include "ssun1.mm"
include "sstri.mm"
include "sseqtr4i.mm"
include "sshjcl.mm"
include "ssun2.mm"
include "chlubii.mm"
include "ococi.mm"
include "sseqtri.mm"
include "eqssi.mm"

theorem sshhococi
  let cA: class A
  let cB: class B
  assume sshjococ.1: |- A C_ ~H
  assume sshjococ.2: |- B C_ ~H


  assert |- ( A vH B ) = ( ( _|_ ` ( _|_ ` A ) ) vH ( _|_ ` ( _|_ ` B ) ) )

  proof
    cA
    cB
    chj
    co
    #
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cort
    cfv
    #
    chj
    co
    #
    cA
    cB
    cun
    #
    cort
    cfv
    cort
    cfv
    #
    @2
    @4
    cun
    #
    cort
    cfv
    cort
    cfv
    #
    @0
    @5
    @6
    @8
    wss
    #
    @7
    @9
    wss
    cA
    @2
    wss
    #
    cB
    @4
    wss
    #
    @10
    cA
    chil
    wss
    #
    @11
    sshjococ.1
    cA
    ococss
    ax-mp
    cB
    chil
    wss
    #
    @12
    sshjococ.2
    cB
    ococss
    ax-mp
    cA
    @2
    cB
    @4
    unss12
    mp2an
    @6
    @8
    cA
    cB
    chil
    sshjococ.1
    sshjococ.2
    unssi
    #
    @2
    @4
    chil
    @2
    @1
    @13
    @1
    cch
    wcel
    sshjococ.1
    cA
    occl
    ax-mp
    choccli
    #
    chssii
    @4
    @3
    @14
    @3
    cch
    wcel
    sshjococ.2
    cB
    occl
    ax-mp
    choccli
    #
    chssii
    unssi
    occon2i
    ax-mp
    @13
    @14
    @0
    @7
    wceq
    sshjococ.1
    sshjococ.2
    cA
    cB
    sshjval
    mp2an
    #
    @2
    @4
    @16
    @17
    chjvali
    3sstr4i
    @5
    @0
    cort
    cfv
    #
    cort
    cfv
    #
    @0
    @2
    @20
    wss
    #
    @4
    @20
    wss
    #
    @5
    @20
    wss
    cA
    @0
    wss
    @21
    cA
    @7
    @0
    cA
    @6
    @7
    cA
    cB
    ssun1
    @6
    chil
    wss
    @6
    @7
    wss
    @15
    @6
    ococss
    ax-mp
    #
    sstri
    @18
    sseqtr4i
    cA
    @0
    sshjococ.1
    @0
    @13
    @14
    @0
    cch
    wcel
    sshjococ.1
    sshjococ.2
    cA
    cB
    sshjcl
    mp2an
    #
    chssii
    #
    occon2i
    ax-mp
    cB
    @0
    wss
    @22
    cB
    @7
    @0
    cB
    @6
    @7
    cB
    cA
    ssun2
    @23
    sstri
    @18
    sseqtr4i
    cB
    @0
    sshjococ.2
    @25
    occon2i
    ax-mp
    @2
    @4
    @20
    @16
    @17
    @19
    @0
    @24
    choccli
    choccli
    chlubii
    mp2an
    @0
    @24
    ococi
    sseqtri
    eqssi
end
