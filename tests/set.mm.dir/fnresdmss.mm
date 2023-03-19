include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "wrel.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "fnrel.mm"
include "adantr.mm"
include "fndm.mm"
include "simpr.mm"
include "eqsstrd.mm"
include "relssres.mm"
include "syl2anc.mm"

theorem fnresdmss
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ A C_ B ) -> ( F |` B ) = F )

  proof
    cF
    cA
    wfn
    #
    cA
    cB
    wss
    #
    wa
    #
    cF
    wrel
    #
    cF
    cdm
    #
    cB
    wss
    cF
    cB
    cres
    cF
    wceq
    @0
    @3
    @1
    cA
    cF
    fnrel
    adantr
    @2
    @4
    cA
    cB
    @0
    @4
    cA
    wceq
    @1
    cA
    cF
    fndm
    adantr
    @0
    @1
    simpr
    eqsstrd
    cF
    cB
    relssres
    syl2anc
end
