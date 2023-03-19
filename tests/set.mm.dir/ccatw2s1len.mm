include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "c2.mm"
include "cvv.mm"
include "wceq.mm"
include "ccatws1clv.mm"
include "ccatws1len.mm"
include "syl.mm"
include "oveq1d.mm"
include "cn0.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cn.mm"
include "add1p1.mm"
include "3syl.mm"
include "3eqtrd.mm"

theorem ccatw2s1len
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( W e. Word V -> ( # ` ( ( W ++ <" X "> ) ++ <" Y "> ) ) = ( ( # ` W ) + 2 ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    cX
    cs1
    cconcat
    co
    #
    cY
    cs1
    cconcat
    co
    chash
    cfv
    #
    @1
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    @5
    c2
    caddc
    co
    #
    @0
    @1
    cvv
    cword
    wcel
    @2
    @4
    wceq
    cV
    cW
    cX
    ccatws1clv
    cvv
    @1
    cY
    ccatws1len
    syl
    @0
    @3
    @6
    c1
    caddc
    cV
    cW
    cX
    ccatws1len
    oveq1d
    @0
    @5
    cn0
    wcel
    @5
    cc
    wcel
    @7
    @8
    wceq
    cV
    cW
    lencl
    @5
    nn0cn
    @5
    add1p1
    3syl
    3eqtrd
end
