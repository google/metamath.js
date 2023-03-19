include "crp.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfl.mm"
include "cfv.mm"
include "caddc.mm"
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
include "syl5eqel.mm"
include "flltp1.mm"
include "syl6breqr.mm"
include "nnrpd.mm"
include "ltrecd.mm"
include "mpbid.mm"
include "rpcn.mm"
include "rpne0.mm"
include "recrecd.mm"
include "breqtrd.mm"
include "jca.mm"

theorem recnnltrp
  let cE: class E
  let cN: class N
  assume recnnltrp.1: |- N = ( ( |_ ` ( 1 / E ) ) + 1 )


  assert |- ( E e. RR+ -> ( N e. NN /\ ( 1 / N ) < E ) )

  proof
    cE
    crp
    wcel
    #
    cN
    cn
    wcel
    c1
    cN
    cdiv
    co
    #
    cE
    clt
    wbr
    @0
    cN
    c1
    cE
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
    recnnltrp.1
    @0
    @3
    cn0
    wcel
    #
    @4
    cn
    wcel
    @0
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    @5
    @0
    @2
    cE
    rpreccl
    #
    rpred
    #
    @0
    @2
    @7
    rpge0d
    @2
    flge0nn0
    syl2anc
    @3
    nn0p1nn
    syl
    syl5eqel
    #
    @0
    @1
    c1
    @2
    cdiv
    co
    #
    cE
    clt
    @0
    @2
    cN
    clt
    wbr
    @1
    @10
    clt
    wbr
    @0
    @2
    @4
    cN
    clt
    @0
    @6
    @2
    @4
    clt
    wbr
    @8
    @2
    flltp1
    syl
    recnnltrp.1
    syl6breqr
    @0
    @2
    cN
    @7
    @0
    cN
    @9
    nnrpd
    ltrecd
    mpbid
    @0
    cE
    cE
    rpcn
    cE
    rpne0
    recrecd
    breqtrd
    jca
end
