include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "ccatws1lenOLD.mm"
include "eqeq1d.mm"
include "wi.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "ex.mm"
include "adantr.mm"
include "sylbid.mm"

theorem ccatws1lenrevOLD
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ X e. V ) -> ( ( # ` ( W ++ <" X "> ) ) = N -> ( # ` W ) = ( N - 1 ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cX
    cV
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
    wceq
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    @4
    cN
    c1
    cmin
    co
    #
    wceq
    #
    @2
    @3
    @5
    cN
    cV
    cW
    cX
    ccatws1lenOLD
    eqeq1d
    @0
    @6
    @8
    wi
    @1
    @0
    @6
    @8
    @0
    @6
    @4
    @5
    c1
    cmin
    co
    #
    @7
    @0
    @4
    cc
    wcel
    @9
    @4
    wceq
    @0
    @4
    cV
    cW
    lencl
    nn0cnd
    @4
    pncan1
    syl
    @5
    cN
    c1
    cmin
    oveq1
    sylan9req
    ex
    adantr
    sylbid
end
