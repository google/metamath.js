include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "fndm.mm"
include "dmeq.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "syl.mm"

theorem fnxpdmdm
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( F Fn ( A X. A ) -> dom dom F = A )

  proof
    cF
    cA
    cA
    cxp
    #
    wfn
    cF
    cdm
    #
    @0
    wceq
    #
    @1
    cdm
    #
    cA
    wceq
    @0
    cF
    fndm
    @2
    @3
    @0
    cdm
    cA
    @1
    @0
    dmeq
    cA
    dmxpid
    syl6eq
    syl
end
