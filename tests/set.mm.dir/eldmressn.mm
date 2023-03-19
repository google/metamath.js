include "wceq.mm"
include "csn.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "elsni.mm"
include "adantr.mm"
include "sylbi.mm"
include "dmres.mm"
include "eleq2s.mm"

theorem eldmressn
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( B e. dom ( F |` { A } ) -> B = A )

  proof
    cB
    cA
    wceq
    #
    cB
    cA
    csn
    #
    cF
    cdm
    #
    cin
    #
    cF
    @1
    cres
    cdm
    cB
    @3
    wcel
    cB
    @1
    wcel
    #
    cB
    @2
    wcel
    #
    wa
    @0
    cB
    @1
    @2
    elin
    @4
    @0
    @5
    cB
    cA
    elsni
    adantr
    sylbi
    cF
    @1
    dmres
    eleq2s
end
