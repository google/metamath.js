include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "c0.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "fn0.mm"
include "fndmu.mm"
include "sylan2br.mm"
include "ex.mm"
include "fneq2.mm"
include "syl6bb.mm"
include "biimpcd.mm"
include "impbid.mm"
include "fz1n.mm"
include "sylan9bbr.mm"

theorem 0fz1
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN0 /\ F Fn ( 1 ... N ) ) -> ( F = (/) <-> N = 0 ) )

  proof
    cF
    c1
    cN
    cfz
    co
    #
    wfn
    #
    cF
    c0
    wceq
    #
    @0
    c0
    wceq
    #
    cN
    cn0
    wcel
    cN
    cc0
    wceq
    @1
    @2
    @3
    @1
    @2
    @3
    @2
    @1
    cF
    c0
    wfn
    #
    @3
    cF
    fn0
    #
    @0
    c0
    cF
    fndmu
    sylan2br
    ex
    @3
    @1
    @2
    @3
    @1
    @4
    @2
    @0
    c0
    cF
    fneq2
    @5
    syl6bb
    biimpcd
    impbid
    cN
    fz1n
    sylan9bbr
end
