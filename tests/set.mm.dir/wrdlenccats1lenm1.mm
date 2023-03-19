include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "ccatws1len.mm"
include "oveq1d.mm"
include "cc.mm"
include "wceq.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "eqtrd.mm"

theorem wrdlenccats1lenm1
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( ( # ` ( W ++ <" S "> ) ) - 1 ) = ( # ` W ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    cS
    cs1
    cconcat
    co
    chash
    cfv
    #
    c1
    cmin
    co
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @2
    @0
    @1
    @3
    c1
    cmin
    cV
    cW
    cS
    ccatws1len
    oveq1d
    @0
    @2
    cc
    wcel
    @4
    @2
    wceq
    @0
    @2
    cV
    cW
    lencl
    nn0cnd
    @2
    pncan1
    syl
    eqtrd
end
