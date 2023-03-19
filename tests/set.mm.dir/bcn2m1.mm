include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cbc.mm"
include "caddc.mm"
include "nnm1nn0.mm"
include "nn0cnd.mm"
include "cn0.mm"
include "cz.mm"
include "2z.mm"
include "bccl.mm"
include "sylancl.mm"
include "addcomd.mm"
include "wceq.mm"
include "bcn1.mm"
include "eqcomd.mm"
include "syl.mm"
include "1e2m1.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "bcpasc.mm"
include "nncn.mm"
include "1cnd.mm"
include "npcand.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem bcn2m1
  let cN: class N


  assert |- ( N e. NN -> ( ( N - 1 ) + ( ( N - 1 ) _C 2 ) ) = ( N _C 2 ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    cmin
    co
    #
    @1
    c2
    cbc
    co
    #
    caddc
    co
    @2
    @1
    caddc
    co
    @2
    @1
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
    c2
    cbc
    co
    #
    @0
    @1
    @2
    @0
    @1
    cN
    nnm1nn0
    #
    nn0cnd
    @0
    @2
    @0
    @1
    cn0
    wcel
    #
    c2
    cz
    wcel
    #
    @2
    cn0
    wcel
    @7
    2z
    c2
    @1
    bccl
    sylancl
    nn0cnd
    addcomd
    @0
    @1
    @4
    @2
    caddc
    @0
    @1
    @1
    c1
    cbc
    co
    #
    @4
    @0
    @8
    @1
    @10
    wceq
    @7
    @8
    @10
    @1
    @1
    bcn1
    eqcomd
    syl
    @0
    c1
    @3
    @1
    cbc
    c1
    @3
    wceq
    @0
    1e2m1
    a1i
    oveq2d
    eqtrd
    oveq2d
    @0
    @5
    @1
    c1
    caddc
    co
    #
    c2
    cbc
    co
    #
    @6
    @0
    @8
    @9
    @5
    @12
    wceq
    @7
    2z
    c2
    @1
    bcpasc
    sylancl
    @0
    @11
    cN
    c2
    cbc
    @0
    cN
    c1
    cN
    nncn
    @0
    1cnd
    npcand
    oveq1d
    eqtrd
    3eqtrd
end
