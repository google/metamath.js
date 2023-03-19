include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "elnn0.mm"
include "cid.mm"
include "cseq.mm"
include "peano2nn.mm"
include "facnn.mm"
include "syl.mm"
include "cvv.mm"
include "ovex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "cuz.mm"
include "seqp1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "oveq1d.mm"
include "3eqtr4a.mm"
include "eqtrd.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "fac1.mm"
include "eqtri.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fac0.mm"
include "oveq12i.mm"
include "1t1e1.mm"
include "syl6eq.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem facp1
  let cN: class N


  assert |- ( N e. NN0 -> ( ! ` ( N + 1 ) ) = ( ( ! ` N ) x. ( N + 1 ) ) )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cN
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cN
    cfa
    cfv
    #
    @2
    cmul
    co
    #
    wceq
    #
    cN
    elnn0
    @0
    @6
    @1
    @0
    @3
    @2
    cmul
    cid
    c1
    cseq
    #
    cfv
    #
    @5
    @0
    @2
    cn
    wcel
    @3
    @8
    wceq
    cN
    peano2nn
    @2
    facnn
    syl
    @0
    cN
    @7
    cfv
    #
    @2
    cid
    cfv
    #
    cmul
    co
    #
    @9
    @2
    cmul
    co
    @8
    @5
    @10
    @2
    @9
    cmul
    @2
    cvv
    wcel
    @10
    @2
    wceq
    cN
    c1
    caddc
    ovex
    @2
    cvv
    fvi
    ax-mp
    oveq2i
    @8
    @11
    wceq
    cN
    c1
    cuz
    cfv
    cn
    cmul
    cid
    c1
    cN
    seqp1
    nnuz
    eleq2s
    @0
    @4
    @9
    @2
    cmul
    cN
    facnn
    oveq1d
    3eqtr4a
    eqtrd
    @1
    cc0
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    c1
    @3
    @5
    @13
    c1
    cfa
    cfv
    c1
    @12
    c1
    cfa
    0p1e1
    fveq2i
    fac1
    eqtri
    @1
    @2
    @12
    cfa
    cN
    cc0
    c1
    caddc
    oveq1
    #
    fveq2d
    @1
    @5
    cc0
    cfa
    cfv
    #
    @12
    cmul
    co
    #
    c1
    @1
    @4
    @15
    @2
    @12
    cmul
    cN
    cc0
    cfa
    fveq2
    @14
    oveq12d
    @16
    c1
    c1
    cmul
    co
    c1
    @15
    c1
    @12
    c1
    cmul
    fac0
    0p1e1
    oveq12i
    1t1e1
    eqtri
    syl6eq
    3eqtr4a
    jaoi
    sylbi
end
