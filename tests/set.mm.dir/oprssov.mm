include "wfun.mm"
include "cxp.mm"
include "wfn.mm"
include "wss.mm"
include "w3a.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "cdm.mm"
include "fndm.mm"
include "reseq2d.mm"
include "3ad2ant2.mm"
include "funssres.mm"
include "3adant2.mm"
include "eqtr3d.mm"
include "oveqd.mm"
include "adantr.mm"

theorem oprssov
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G


  assert |- ( ( ( Fun F /\ G Fn ( C X. D ) /\ G C_ F ) /\ ( A e. C /\ B e. D ) ) -> ( A F B ) = ( A G B ) )

  proof
    cF
    wfun
    #
    cG
    cC
    cD
    cxp
    #
    wfn
    #
    cG
    cF
    wss
    #
    w3a
    #
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    wa
    cA
    cB
    cF
    @1
    cres
    #
    co
    #
    cA
    cB
    cF
    co
    #
    cA
    cB
    cG
    co
    #
    @5
    @7
    @8
    wceq
    @4
    cA
    cB
    cC
    cD
    cF
    ovres
    adantl
    @4
    @7
    @9
    wceq
    @5
    @4
    @6
    cG
    cA
    cB
    @4
    cF
    cG
    cdm
    #
    cres
    #
    @6
    cG
    @2
    @0
    @11
    @6
    wceq
    @3
    @2
    @10
    @1
    cF
    @1
    cG
    fndm
    reseq2d
    3ad2ant2
    @0
    @3
    @11
    cG
    wceq
    @2
    cF
    cG
    funssres
    3adant2
    eqtr3d
    oveqd
    adantr
    eqtr3d
end
