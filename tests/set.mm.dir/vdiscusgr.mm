include "cfusgr.mm"
include "wcel.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "ccusgr.mm"
include "wa.mm"
include "cuvtx.mm"
include "uvtxisvtx.mm"
include "wi.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspccv.mm"
include "adantl.mm"
include "imp.mm"
include "wb.mm"
include "usgruvtxvdb.mm"
include "adantlr.mm"
include "mpbird.mm"
include "ex.mm"
include "impbid2.mm"
include "eqrdv.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "cusgruvtxb.mm"
include "syl.mm"
include "adantr.mm"

theorem vdiscusgr
  let vv: setvar v
  let cG: class G
  let cV: class V
  let ve: setvar e
  let cU: class U
  let vn: setvar n
  assume hashnbusgrvd.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G e
  disjoint U e
  disjoint V e
  disjoint G n
  disjoint n v
  disjoint V n
  assert |- ( G e. FinUSGraph -> ( A. v e. V ( ( VtxDeg ` G ) ` v ) = ( ( # ` V ) - 1 ) -> G e. ComplUSGraph ) )

  proof
    cG
    cfusgr
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cV
    chash
    cfv
    c1
    cmin
    co
    #
    wceq
    #
    vv
    cV
    wral
    #
    cG
    ccusgr
    wcel
    #
    @0
    @6
    wa
    #
    @7
    cG
    cuvtx
    cfv
    #
    cV
    wceq
    #
    @8
    vn
    @9
    cV
    @8
    vn
    cv
    #
    @9
    wcel
    #
    @11
    cV
    wcel
    #
    cG
    @11
    cV
    hashnbusgrvd.v
    uvtxisvtx
    @8
    @13
    @12
    @8
    @13
    wa
    @12
    @11
    @2
    cfv
    #
    @4
    wceq
    #
    @8
    @13
    @15
    @6
    @13
    @15
    wi
    @0
    @5
    @15
    vv
    @11
    cV
    vv
    vn
    weq
    @3
    @14
    @4
    @1
    @11
    @2
    fveq2
    eqeq1d
    rspccv
    adantl
    imp
    @0
    @13
    @12
    @15
    wb
    @6
    @11
    cG
    cV
    hashnbusgrvd.v
    usgruvtxvdb
    adantlr
    mpbird
    ex
    impbid2
    eqrdv
    @0
    @7
    @10
    wb
    #
    @6
    @0
    cG
    cusgr
    wcel
    @16
    cG
    fusgrusgr
    cG
    cV
    hashnbusgrvd.v
    cusgruvtxb
    syl
    adantr
    mpbird
    ex
end
