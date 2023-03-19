include "cop.mm"
include "cpr.mm"
include "wss.mm"
include "csn.mm"
include "wceq.mm"
include "dfop.mm"
include "sseq2i.mm"
include "c0.mm"
include "wo.mm"
include "sspr.mm"
include "wne.mm"
include "opex.mm"
include "prnz.mm"
include "eqneqall.mm"
include "mpi.mm"
include "wa.mm"
include "snex.mm"
include "preqsn.mm"
include "opth.mm"
include "simpl.mm"
include "sylbi.mm"
include "adantr.mm"
include "jaoi.mm"
include "prex.mm"
include "wi.mm"
include "a1d.mm"
include "imp.mm"
include "eqcomi.mm"
include "eqeq2i.mm"
include "propeqop.mm"
include "bitri.mm"
include "simpll.mm"

theorem propssopi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume snopeqop.a: |- A e. _V
  assume snopeqop.b: |- B e. _V
  assume snopeqop.c: |- C e. _V
  assume snopeqop.d: |- D e. _V
  assume propeqop.e: |- E e. _V
  assume propeqop.f: |- F e. _V


  assert |- ( { <. A , B >. , <. C , D >. } C_ <. E , F >. -> A = C )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cpr
    #
    cE
    cF
    cop
    #
    wss
    @2
    cE
    csn
    #
    cE
    cF
    cpr
    #
    cpr
    #
    wss
    #
    cA
    cC
    wceq
    #
    @3
    @6
    @2
    cE
    cF
    propeqop.e
    propeqop.f
    dfop
    #
    sseq2i
    @7
    @2
    c0
    wceq
    #
    @2
    @4
    csn
    wceq
    #
    wo
    #
    @2
    @5
    csn
    wceq
    #
    @2
    @6
    wceq
    #
    wo
    #
    wo
    @8
    @2
    @4
    @5
    sspr
    @12
    @8
    @15
    @10
    @8
    @11
    @10
    @2
    c0
    wne
    @8
    @0
    @1
    cA
    cB
    opex
    #
    prnz
    @8
    @2
    c0
    eqneqall
    mpi
    @11
    @0
    @1
    wceq
    #
    @1
    @4
    wceq
    #
    wa
    @8
    @0
    @1
    @4
    @16
    cC
    cD
    opex
    #
    cE
    snex
    preqsn
    @17
    @8
    @18
    @17
    @8
    cB
    cD
    wceq
    #
    wa
    #
    @8
    cA
    cB
    cC
    cD
    snopeqop.a
    snopeqop.b
    opth
    #
    @8
    @20
    simpl
    #
    sylbi
    adantr
    sylbi
    jaoi
    @13
    @8
    @14
    @13
    @17
    @1
    @5
    wceq
    #
    wa
    @8
    @0
    @1
    @5
    @16
    @19
    cE
    cF
    prex
    preqsn
    @17
    @24
    @8
    @17
    @21
    @24
    @8
    wi
    @22
    @21
    @8
    @24
    @23
    a1d
    sylbi
    imp
    sylbi
    @14
    @8
    cE
    cA
    csn
    wceq
    #
    wa
    cA
    cB
    wceq
    cF
    cA
    cD
    cpr
    wceq
    wa
    cA
    cD
    wceq
    cF
    cA
    cB
    cpr
    wceq
    wa
    wo
    #
    wa
    #
    @8
    @14
    @2
    @3
    wceq
    @27
    @6
    @3
    @2
    @3
    @6
    @9
    eqcomi
    eqeq2i
    cA
    cB
    cC
    cD
    cE
    cF
    snopeqop.a
    snopeqop.b
    snopeqop.c
    snopeqop.d
    propeqop.e
    propeqop.f
    propeqop
    bitri
    @8
    @25
    @26
    simpll
    sylbi
    jaoi
    jaoi
    sylbi
    sylbi
end
