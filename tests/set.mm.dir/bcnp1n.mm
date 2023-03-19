include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cbc.mm"
include "cmin.mm"
include "cz.mm"
include "wceq.mm"
include "peano2nn0.mm"
include "nn0z.mm"
include "bccmpl.mm"
include "syl2anc.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "bcn1.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem bcnp1n
  let cN: class N


  assert |- ( N e. NN0 -> ( ( N + 1 ) _C N ) = ( N + 1 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cN
    cbc
    co
    #
    @1
    @1
    cN
    cmin
    co
    #
    cbc
    co
    #
    @1
    c1
    cbc
    co
    #
    @1
    @0
    @1
    cn0
    wcel
    #
    cN
    cz
    wcel
    @2
    @4
    wceq
    cN
    peano2nn0
    #
    cN
    nn0z
    cN
    @1
    bccmpl
    syl2anc
    @0
    @3
    c1
    @1
    cbc
    @0
    cN
    cc
    wcel
    c1
    cc
    wcel
    @3
    c1
    wceq
    cN
    nn0cn
    ax-1cn
    cN
    c1
    pncan2
    sylancl
    oveq2d
    @0
    @6
    @5
    @1
    wceq
    @7
    @1
    bcn1
    syl
    3eqtrd
end
