include "cfusgr.mm"
include "wcel.mm"
include "ccusgr.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "wral.mm"
include "cvtxdg.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cusgr.mm"
include "wb.mm"
include "fusgrusgr.mm"
include "wss.mm"
include "cusgruvtxb.mm"
include "uvtxssvtx.mm"
include "sssseq.mm"
include "eqcom.mm"
include "syl6rbbr.mm"
include "mp1i.mm"
include "bitrd.mm"
include "dfss3.mm"
include "syl6bb.mm"
include "syl.mm"
include "usgruvtxvdb.mm"
include "ralbidva.mm"

theorem vdiscusgrb
  let vv: setvar v
  let cG: class G
  let cV: class V
  let ve: setvar e
  let cU: class U
  assume hashnbusgrvd.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint G e
  disjoint U e
  disjoint V e
  assert |- ( G e. FinUSGraph -> ( G e. ComplUSGraph <-> A. v e. V ( ( VtxDeg ` G ) ` v ) = ( ( # ` V ) - 1 ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cG
    ccusgr
    wcel
    #
    vv
    cv
    #
    cG
    cuvtx
    cfv
    #
    wcel
    #
    vv
    cV
    wral
    #
    @2
    cG
    cvtxdg
    cfv
    cfv
    cV
    chash
    cfv
    c1
    cmin
    co
    wceq
    #
    vv
    cV
    wral
    @0
    cG
    cusgr
    wcel
    #
    @1
    @5
    wb
    cG
    fusgrusgr
    @7
    @1
    cV
    @3
    wss
    #
    @5
    @7
    @1
    @3
    cV
    wceq
    #
    @8
    cG
    cV
    hashnbusgrvd.v
    cusgruvtxb
    @3
    cV
    wss
    #
    @9
    @8
    wb
    @7
    cG
    cV
    hashnbusgrvd.v
    uvtxssvtx
    @10
    @8
    cV
    @3
    wceq
    @9
    cV
    @3
    sssseq
    @3
    cV
    eqcom
    syl6rbbr
    mp1i
    bitrd
    vv
    cV
    @3
    dfss3
    syl6bb
    syl
    @0
    @4
    @6
    vv
    cV
    @2
    cG
    cV
    hashnbusgrvd.v
    usgruvtxvdb
    ralbidva
    bitrd
end
