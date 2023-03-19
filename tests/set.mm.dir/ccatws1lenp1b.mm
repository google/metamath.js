include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "ccatws1len.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "nn0cn.mm"
include "adantl.mm"
include "1cnd.mm"
include "addcan2d.mm"
include "bitrd.mm"

theorem ccatws1lenp1b
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ N e. NN0 ) -> ( ( # ` ( W ++ <" X "> ) ) = ( N + 1 ) <-> ( # ` W ) = N ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cW
    cX
    cs1
    cconcat
    co
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @4
    wceq
    @5
    cN
    wceq
    @2
    @3
    @6
    @4
    @0
    @3
    @6
    wceq
    @1
    cV
    cW
    cX
    ccatws1len
    adantr
    eqeq1d
    @2
    @5
    cN
    c1
    @0
    @5
    cc
    wcel
    @1
    @0
    @5
    cV
    cW
    lencl
    nn0cnd
    adantr
    @1
    cN
    cc
    wcel
    @0
    cN
    nn0cn
    adantl
    @2
    1cnd
    addcan2d
    bitrd
end
