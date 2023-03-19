include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "ce.mm"
include "clt.mm"
include "cc.mm"
include "wceq.mm"
include "rpcn.mm"
include "nn0uz.mm"
include "0nn0.mm"
include "1e0p1.mm"
include "0z.mm"
include "eqid.mm"
include "eftval.mm"
include "ax-mp.mm"
include "eft0val.mm"
include "syl5eq.mm"
include "seq1i.mm"
include "1nn0.mm"
include "fac1.mm"
include "oveq2i.mm"
include "exp1.mm"
include "oveq1d.mm"
include "div1.mm"
include "eqtrd.mm"
include "seqp1i.mm"
include "syl.mm"
include "id.mm"
include "a1i.mm"
include "effsumlt.mm"
include "eqbrtrrd.mm"

theorem efgt1p
  let cA: class A
  let vn: setvar n


  assert |- ( A e. RR+ -> ( 1 + A ) < ( exp ` A ) )

  proof
    cA
    crp
    wcel
    #
    c1
    caddc
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    @1
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cc0
    cseq
    cfv
    #
    c1
    cA
    caddc
    co
    #
    cA
    ce
    cfv
    clt
    @0
    cA
    cc
    wcel
    #
    @3
    @4
    wceq
    cA
    rpcn
    @5
    c1
    cA
    caddc
    @2
    c1
    cc0
    cc0
    cn0
    nn0uz
    0nn0
    1e0p1
    @5
    c1
    caddc
    @2
    cc0
    0z
    @5
    cc0
    @2
    cfv
    #
    cA
    cc0
    cexp
    co
    cc0
    cfa
    cfv
    cdiv
    co
    #
    c1
    cc0
    cn0
    wcel
    @6
    @7
    wceq
    0nn0
    cA
    vn
    @2
    cc0
    @2
    eqid
    #
    eftval
    ax-mp
    cA
    eft0val
    syl5eq
    seq1i
    @5
    c1
    @2
    cfv
    #
    cA
    c1
    cexp
    co
    #
    c1
    cfa
    cfv
    #
    cdiv
    co
    #
    cA
    c1
    cn0
    wcel
    #
    @9
    @12
    wceq
    1nn0
    cA
    vn
    @2
    c1
    @8
    eftval
    ax-mp
    @5
    @12
    @10
    c1
    cdiv
    co
    #
    cA
    @11
    c1
    @10
    cdiv
    fac1
    oveq2i
    @5
    @14
    cA
    c1
    cdiv
    co
    cA
    @5
    @10
    cA
    c1
    cdiv
    cA
    exp1
    oveq1d
    cA
    div1
    eqtrd
    syl5eq
    syl5eq
    seqp1i
    syl
    @0
    cA
    vn
    @2
    c1
    @8
    @0
    id
    @13
    @0
    1nn0
    a1i
    effsumlt
    eqbrtrrd
end
