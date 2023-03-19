include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "ccatws1lenOLD.mm"
include "oveq1d.mm"
include "wceq.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "adantr.mm"
include "eqtr2d.mm"

theorem wrdlenccats1lenm1OLD
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ S e. V ) -> ( # ` W ) = ( ( # ` ( W ++ <" S "> ) ) - 1 ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cS
    cV
    wcel
    #
    wa
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
    @4
    @2
    @3
    @5
    c1
    cmin
    cV
    cW
    cS
    ccatws1lenOLD
    oveq1d
    @0
    @6
    @4
    wceq
    #
    @1
    @0
    @4
    cc
    wcel
    @7
    @0
    @4
    cV
    cW
    lencl
    nn0cnd
    @4
    pncan1
    syl
    adantr
    eqtr2d
end
