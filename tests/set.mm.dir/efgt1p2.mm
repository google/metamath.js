include "crp.mm"
include "wcel.mm"
include "c2.mm"
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
include "c1.mm"
include "ce.mm"
include "clt.mm"
include "nn0uz.mm"
include "1nn0.mm"
include "df-2.mm"
include "cc.mm"
include "wceq.mm"
include "rpcn.mm"
include "0nn0.mm"
include "1e0p1.mm"
include "0z.mm"
include "eqid.mm"
include "eftval.mm"
include "ax-mp.mm"
include "eft0val.mm"
include "syl5eq.mm"
include "seq1i.mm"
include "fac1.mm"
include "oveq2i.mm"
include "exp1.mm"
include "oveq1d.mm"
include "div1.mm"
include "eqtrd.mm"
include "seqp1i.mm"
include "syl.mm"
include "2nn0.mm"
include "fac2.mm"
include "eqtri.mm"
include "a1i.mm"
include "id.mm"
include "effsumlt.mm"
include "eqbrtrrd.mm"

theorem efgt1p2
  let cA: class A
  let vn: setvar n


  assert |- ( A e. RR+ -> ( ( 1 + A ) + ( ( A ^ 2 ) / 2 ) ) < ( exp ` A ) )

  proof
    cA
    crp
    wcel
    #
    c2
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
    #
    cfv
    c1
    cA
    caddc
    co
    #
    cA
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    caddc
    co
    cA
    ce
    cfv
    clt
    @0
    @4
    @6
    caddc
    @2
    c2
    cc0
    c1
    cn0
    nn0uz
    1nn0
    df-2
    @0
    cA
    cc
    wcel
    #
    c1
    @3
    cfv
    @4
    wceq
    cA
    rpcn
    @7
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
    @7
    c1
    caddc
    @2
    cc0
    0z
    @7
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
    @8
    @9
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
    @7
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
    @11
    @14
    wceq
    1nn0
    cA
    vn
    @2
    c1
    @10
    eftval
    ax-mp
    @7
    @14
    @12
    c1
    cdiv
    co
    #
    cA
    @13
    c1
    @12
    cdiv
    fac1
    oveq2i
    @7
    @15
    cA
    c1
    cdiv
    co
    cA
    @7
    @12
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
    c2
    @2
    cfv
    #
    @6
    wceq
    @0
    @16
    @5
    c2
    cfa
    cfv
    #
    cdiv
    co
    #
    @6
    c2
    cn0
    wcel
    #
    @16
    @18
    wceq
    2nn0
    cA
    vn
    @2
    c2
    @10
    eftval
    ax-mp
    @17
    c2
    @5
    cdiv
    fac2
    oveq2i
    eqtri
    a1i
    seqp1i
    @0
    cA
    vn
    @2
    c2
    @10
    @0
    id
    @19
    @0
    2nn0
    a1i
    effsumlt
    eqbrtrrd
end
