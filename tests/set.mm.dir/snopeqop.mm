include "wceq.mm"
include "cop.mm"
include "csn.mm"
include "wa.mm"
include "w3a.mm"
include "opeqsn.mm"
include "anbi2i.mm"
include "eqcom.mm"
include "opex.mm"
include "bitri.mm"
include "3anan12.mm"
include "3bitr4i.mm"

theorem snopeqop
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume snopeqop.a: |- A e. _V
  assume snopeqop.b: |- B e. _V
  assume snopeqop.c: |- C e. _V
  assume snopeqop.d: |- D e. _V


  assert |- ( { <. A , B >. } = <. C , D >. <-> ( A = B /\ C = D /\ C = { A } ) )

  proof
    cC
    cD
    wceq
    #
    cA
    cB
    cop
    #
    cC
    csn
    wceq
    #
    wa
    #
    @0
    cA
    cB
    wceq
    #
    cC
    cA
    csn
    wceq
    #
    wa
    #
    wa
    @1
    csn
    #
    cC
    cD
    cop
    #
    wceq
    #
    @4
    @0
    @5
    w3a
    @2
    @6
    @0
    cA
    cB
    cC
    snopeqop.a
    snopeqop.b
    snopeqop.c
    opeqsn
    anbi2i
    @9
    @8
    @7
    wceq
    @3
    @7
    @8
    eqcom
    cC
    cD
    @1
    snopeqop.c
    snopeqop.d
    cA
    cB
    opex
    opeqsn
    bitri
    @4
    @0
    @5
    3anan12
    3bitr4i
end
