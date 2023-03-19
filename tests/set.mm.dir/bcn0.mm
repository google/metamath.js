include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cbc.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "c1.mm"
include "cfz.mm"
include "wceq.mm"
include "0elfz.mm"
include "bcval2.mm"
include "syl.mm"
include "nn0cn.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "fac0.mm"
include "oveq12.mm"
include "sylancl.mm"
include "faccl.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "facne0.mm"
include "dividd.mm"

theorem bcn0
  let cN: class N


  assert |- ( N e. NN0 -> ( N _C 0 ) = 1 )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    cbc
    co
    #
    cN
    cfa
    cfv
    #
    cN
    cc0
    cmin
    co
    #
    cfa
    cfv
    #
    cc0
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    c1
    @0
    cc0
    cc0
    cN
    cfz
    co
    wcel
    @1
    @7
    wceq
    cN
    0elfz
    cc0
    cN
    bcval2
    syl
    @0
    @7
    @2
    @2
    cdiv
    co
    c1
    @0
    @6
    @2
    @2
    cdiv
    @0
    @6
    @2
    c1
    cmul
    co
    #
    @2
    @0
    @4
    @2
    wceq
    @5
    c1
    wceq
    @6
    @8
    wceq
    @0
    @3
    cN
    cfa
    @0
    cN
    cN
    nn0cn
    subid1d
    fveq2d
    fac0
    @4
    @2
    @5
    c1
    cmul
    oveq12
    sylancl
    @0
    @2
    @0
    @2
    cN
    faccl
    nncnd
    #
    mulid1d
    eqtrd
    oveq2d
    @0
    @2
    @9
    cN
    facne0
    dividd
    eqtrd
    eqtrd
end
