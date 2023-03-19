include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cbc.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cc0.mm"
include "cfz.mm"
include "wceq.mm"
include "fzctr.mm"
include "bcval2.mm"
include "syl.mm"
include "caddc.mm"
include "nn0cn.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "oveq2d.mm"

theorem bcctr
  let cN: class N


  assert |- ( N e. NN0 -> ( ( 2 x. N ) _C N ) = ( ( ! ` ( 2 x. N ) ) / ( ( ! ` N ) x. ( ! ` N ) ) ) )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    cmul
    co
    #
    cN
    cbc
    co
    #
    @1
    cfa
    cfv
    #
    @1
    cN
    cmin
    co
    #
    cfa
    cfv
    #
    cN
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @3
    @6
    @6
    cmul
    co
    #
    cdiv
    co
    @0
    cN
    cc0
    @1
    cfz
    co
    wcel
    @2
    @8
    wceq
    cN
    fzctr
    cN
    @1
    bcval2
    syl
    @0
    @7
    @9
    @3
    cdiv
    @0
    @5
    @6
    @6
    cmul
    @0
    @4
    cN
    cfa
    @0
    @4
    cN
    cN
    caddc
    co
    #
    cN
    cmin
    co
    cN
    @0
    @1
    @10
    cN
    cmin
    @0
    cN
    cN
    nn0cn
    #
    2timesd
    oveq1d
    @0
    cN
    cN
    @11
    @11
    pncand
    eqtrd
    fveq2d
    oveq1d
    oveq2d
    eqtrd
end
