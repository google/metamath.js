include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfrgr.mm"
include "crusgr.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "cvtxdg.mm"
include "wral.mm"
include "w3a.mm"
include "cxnn0.mm"
include "crgr.mm"
include "rusgrrgr.mm"
include "eqid.mm"
include "rgrprop.mm"
include "syl.mm"
include "simprd.mm"
include "frrusgrord0.mm"
include "syl5.mm"
include "3expb.mm"
include "expcom.mm"
include "impd.mm"

theorem frrusgrord
  let cG: class G
  let cK: class K
  let cV: class V
  let vv: setvar v
  assume frrusgrord0.v: |- V = ( Vtx ` G )


  assert |- ( ( V e. Fin /\ V =/= (/) ) -> ( ( G e. FriendGraph /\ G RegUSGraph K ) -> ( # ` V ) = ( ( K x. ( K - 1 ) ) + 1 ) ) )

  proof
    cV
    cfn
    wcel
    #
    cV
    c0
    wne
    #
    wa
    #
    cG
    cfrgr
    wcel
    #
    cG
    cK
    crusgr
    wbr
    #
    cV
    chash
    cfv
    cK
    cK
    c1
    cmin
    co
    cmul
    co
    c1
    caddc
    co
    wceq
    #
    @3
    @2
    @4
    @5
    wi
    #
    @3
    @0
    @1
    @6
    @4
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    cK
    wceq
    vv
    cV
    wral
    #
    @3
    @0
    @1
    w3a
    @5
    @4
    cK
    cxnn0
    wcel
    #
    @8
    @4
    cG
    cK
    crgr
    wbr
    @9
    @8
    wa
    cG
    cK
    rusgrrgr
    vv
    @7
    cG
    cK
    cV
    frrusgrord0.v
    @7
    eqid
    rgrprop
    syl
    simprd
    vv
    cG
    cK
    cV
    frrusgrord0.v
    frrusgrord0
    syl5
    3expb
    expcom
    impd
end
