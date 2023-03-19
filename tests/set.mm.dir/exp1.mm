include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "cmul.mm"
include "cseq.mm"
include "wceq.mm"
include "1nn.mm"
include "expnnval.mm"
include "mpan2.mm"
include "cz.mm"
include "1z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "fvconst2g.mm"
include "eqtrd.mm"

theorem exp1
  let cA: class A


  assert |- ( A e. CC -> ( A ^ 1 ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    cexp
    co
    #
    c1
    cn
    cA
    csn
    cxp
    #
    cfv
    #
    cA
    @0
    @1
    c1
    cmul
    @2
    c1
    cseq
    cfv
    #
    @3
    @0
    c1
    cn
    wcel
    #
    @1
    @4
    wceq
    1nn
    cA
    c1
    expnnval
    mpan2
    c1
    cz
    wcel
    @4
    @3
    wceq
    1z
    cmul
    @2
    c1
    seq1
    ax-mp
    syl6eq
    @0
    @5
    @3
    cA
    wceq
    1nn
    cn
    cA
    c1
    cc
    fvconst2g
    mpan2
    eqtrd
end
