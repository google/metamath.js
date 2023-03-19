include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cmin.mm"
include "nn0cn.mm"
include "cz.mm"
include "2z.mm"
include "bccl.mm"
include "mpan2.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "bcn1.mm"
include "wceq.mm"
include "1e2m1.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "bcpasc.mm"
include "3eqtrd.mm"

theorem bcn2p1
  let cN: class N


  assert |- ( N e. NN0 -> ( N + ( N _C 2 ) ) = ( ( N + 1 ) _C 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cN
    c2
    cbc
    co
    #
    caddc
    co
    @1
    cN
    caddc
    co
    @1
    cN
    c2
    c1
    cmin
    co
    #
    cbc
    co
    #
    caddc
    co
    #
    cN
    c1
    caddc
    co
    c2
    cbc
    co
    #
    @0
    cN
    @1
    cN
    nn0cn
    @0
    @1
    @0
    c2
    cz
    wcel
    #
    @1
    cn0
    wcel
    2z
    c2
    cN
    bccl
    mpan2
    nn0cnd
    addcomd
    @0
    cN
    @3
    @1
    caddc
    @0
    cN
    c1
    cbc
    co
    cN
    @3
    cN
    bcn1
    @0
    c1
    @2
    cN
    cbc
    c1
    @2
    wceq
    @0
    1e2m1
    a1i
    oveq2d
    eqtr3d
    oveq2d
    @0
    @6
    @4
    @5
    wceq
    2z
    c2
    cN
    bcpasc
    mpan2
    3eqtrd
end
