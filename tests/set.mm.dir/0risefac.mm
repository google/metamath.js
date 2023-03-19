include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "crisefac.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "cfallfac.mm"
include "cmul.mm"
include "cc.mm"
include "cn0.mm"
include "wceq.mm"
include "0cn.mm"
include "nnnn0.mm"
include "risefallfac.mm"
include "sylancr.mm"
include "neg0.mm"
include "oveq1i.mm"
include "0fallfac.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "neg1cn.mm"
include "expcl.mm"
include "mul01d.mm"
include "3eqtrd.mm"

theorem 0risefac
  let cN: class N


  assert |- ( N e. NN -> ( 0 RiseFac N ) = 0 )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    crisefac
    co
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    cc0
    cneg
    #
    cN
    cfallfac
    co
    #
    cmul
    co
    #
    @3
    cc0
    cmul
    co
    cc0
    @0
    cc0
    cc
    wcel
    cN
    cn0
    wcel
    #
    @1
    @6
    wceq
    0cn
    cN
    nnnn0
    #
    cN
    cc0
    risefallfac
    sylancr
    @0
    @5
    cc0
    @3
    cmul
    @0
    @5
    cc0
    cN
    cfallfac
    co
    cc0
    @4
    cc0
    cN
    cfallfac
    neg0
    oveq1i
    cN
    0fallfac
    syl5eq
    oveq2d
    @0
    @3
    @0
    @2
    cc
    wcel
    @7
    @3
    cc
    wcel
    neg1cn
    @8
    @2
    cN
    expcl
    sylancr
    mul01d
    3eqtrd
end
