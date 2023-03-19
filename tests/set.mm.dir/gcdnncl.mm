include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "simpl.mm"
include "nnzd.mm"
include "simpr.mm"
include "nnne0d.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"

theorem gcdnncl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN ) -> ( M gcd N ) e. NN )

  proof
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    wn
    cM
    cN
    cgcd
    co
    cn
    wcel
    @2
    cM
    @0
    @1
    simpl
    nnzd
    @2
    cN
    @0
    @1
    simpr
    #
    nnzd
    @2
    @4
    @3
    @2
    cN
    cc0
    @2
    cN
    @5
    nnne0d
    neneqd
    intnand
    cM
    cN
    gcdn0cl
    syl21anc
end
