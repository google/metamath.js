include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "caddc.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "cn0.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "rpreccl.mm"
include "rpred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "flltp1.mm"
include "nnrpd.mm"
include "ltrecd.mm"
include "mpbid.mm"
include "rpcn.mm"
include "rpne0.mm"
include "recrecd.mm"
include "breqtrd.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "rspcev.mm"

theorem rpgtrecnn
  let cA: class A
  let vn: setvar n

  disjoint A n
  assert |- ( A e. RR+ -> E. n e. NN ( 1 / n ) < A )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    c1
    @3
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    vn
    cn
    wrex
    @0
    @2
    cn0
    wcel
    #
    @4
    @0
    @1
    cr
    wcel
    #
    cc0
    @1
    cle
    wbr
    @10
    @0
    @1
    cA
    rpreccl
    #
    rpred
    #
    @0
    @1
    @12
    rpge0d
    @1
    flge0nn0
    syl2anc
    @2
    nn0p1nn
    syl
    #
    @0
    @5
    c1
    @1
    cdiv
    co
    #
    cA
    clt
    @0
    @1
    @3
    clt
    wbr
    #
    @5
    @15
    clt
    wbr
    @0
    @11
    @16
    @13
    @1
    flltp1
    syl
    @0
    @1
    @3
    @12
    @0
    @3
    @14
    nnrpd
    ltrecd
    mpbid
    @0
    cA
    cA
    rpcn
    cA
    rpne0
    recrecd
    breqtrd
    @9
    @6
    vn
    @3
    cn
    @7
    @3
    wceq
    @8
    @5
    cA
    clt
    @7
    @3
    c1
    cdiv
    oveq2
    breq1d
    rspcev
    syl2anc
end
