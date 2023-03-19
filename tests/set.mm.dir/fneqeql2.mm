include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cin.mm"
include "cdm.mm"
include "wss.mm"
include "fneqeql.mm"
include "inss1.mm"
include "dmss.mm"
include "ax-mp.mm"
include "fndm.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "biantrurd.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem fneqeql2
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x


  assert |- ( ( F Fn A /\ G Fn A ) -> ( F = G <-> A C_ dom ( F i^i G ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    #
    cF
    cG
    wceq
    cF
    cG
    cin
    #
    cdm
    #
    cA
    wceq
    #
    cA
    @4
    wss
    #
    cA
    cF
    cG
    fneqeql
    @2
    @6
    @4
    cA
    wss
    #
    @6
    wa
    @5
    @2
    @7
    @6
    @2
    cF
    cdm
    #
    @4
    cA
    @3
    cF
    wss
    @4
    @8
    wss
    cF
    cG
    inss1
    @3
    cF
    dmss
    ax-mp
    @0
    @8
    cA
    wceq
    @1
    cA
    cF
    fndm
    adantr
    syl5sseq
    biantrurd
    @4
    cA
    eqss
    syl6rbbr
    bitrd
end
