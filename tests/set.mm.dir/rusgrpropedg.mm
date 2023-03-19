include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "cxnn0.mm"
include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wel.mm"
include "cedg.mm"
include "crab.mm"
include "rusgrpropnb.mm"
include "wa.mm"
include "wi.mm"
include "eqid.mm"
include "nbedgusgr.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "adantr.mm"
include "imdistani.mm"
include "df-3an.mm"
include "3imtr4i.mm"
include "syl.mm"

theorem rusgrpropedg
  let vv: setvar v
  let ve: setvar e
  let cG: class G
  let cK: class K
  let cV: class V
  assume rusgrpropnb.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint K v
  disjoint G e
  disjoint e v
  assert |- ( G RegUSGraph K -> ( G e. USGraph /\ K e. NN0* /\ A. v e. V ( # ` { e e. ( Edg ` G ) | v e. e } ) = K ) )

  proof
    cG
    cK
    crusgr
    wbr
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    cG
    vv
    cv
    #
    cnbgr
    co
    chash
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    w3a
    #
    @0
    @1
    vv
    ve
    wel
    ve
    cG
    cedg
    cfv
    #
    crab
    chash
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    w3a
    #
    vv
    cG
    cK
    cV
    rusgrpropnb.v
    rusgrpropnb
    @0
    @1
    wa
    #
    @5
    wa
    @12
    @10
    wa
    @6
    @11
    @12
    @5
    @10
    @0
    @5
    @10
    wi
    @1
    @0
    @4
    @9
    vv
    cV
    @0
    @2
    cV
    wcel
    wa
    #
    @4
    @9
    @13
    @3
    @8
    cK
    @2
    ve
    @7
    cG
    cV
    rusgrpropnb.v
    @7
    eqid
    nbedgusgr
    eqeq1d
    biimpd
    ralimdva
    adantr
    imdistani
    @0
    @1
    @5
    df-3an
    @0
    @1
    @10
    df-3an
    3imtr4i
    syl
end
