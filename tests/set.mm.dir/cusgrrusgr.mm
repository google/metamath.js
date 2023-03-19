include "ccusgr.mm"
include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "cv.mm"
include "cvtxdg.mm"
include "wceq.mm"
include "wral.mm"
include "cusgrusgr.mm"
include "3ad2ant1.mm"
include "cn.mm"
include "hashnncl.mm"
include "nnm1nn0.mm"
include "nn0xnn0d.mm"
include "syl6bir.mm"
include "imp.mm"
include "3adant1.mm"
include "cnbgr.mm"
include "csn.mm"
include "cdif.mm"
include "ccplgr.mm"
include "cusgrcplgr.mm"
include "nbcplgr.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "wa.mm"
include "anim1i.mm"
include "adantr.mm"
include "hashnbusgrvd.mm"
include "syl.mm"
include "fveq2.mm"
include "hashdifsn.mm"
include "3ad2antl2.mm"
include "sylan9eqr.mm"
include "eqtr3d.mm"
include "ex.mm"
include "ralimdva.mm"
include "mpd.mm"
include "cvv.mm"
include "wb.mm"
include "simp1.mm"
include "ovex.mm"
include "eqid.mm"
include "isrusgr0.mm"
include "sylancl.mm"
include "mpbir3and.mm"

theorem cusgrrusgr
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume cusgrrusgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. ComplUSGraph /\ V e. Fin /\ V =/= (/) ) -> G RegUSGraph ( ( # ` V ) - 1 ) )

  proof
    cG
    ccusgr
    wcel
    #
    cV
    cfn
    wcel
    #
    cV
    c0
    wne
    #
    w3a
    #
    cG
    cV
    chash
    cfv
    #
    c1
    cmin
    co
    #
    crusgr
    wbr
    #
    cG
    cusgr
    wcel
    #
    @5
    cxnn0
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
    @5
    wceq
    #
    vv
    cV
    wral
    #
    @0
    @1
    @7
    @2
    cG
    cusgrusgr
    3ad2ant1
    #
    @1
    @2
    @8
    @0
    @1
    @2
    @8
    @1
    @2
    @4
    cn
    wcel
    #
    @8
    cV
    hashnncl
    @15
    @5
    @4
    nnm1nn0
    nn0xnn0d
    syl6bir
    imp
    3adant1
    @3
    cG
    @9
    cnbgr
    co
    #
    cV
    @9
    csn
    cdif
    #
    wceq
    #
    vv
    cV
    wral
    @13
    @3
    @18
    vv
    cV
    @3
    cG
    ccplgr
    wcel
    #
    @9
    cV
    wcel
    #
    @18
    @0
    @1
    @19
    @2
    cG
    cusgrcplgr
    3ad2ant1
    cG
    @9
    cV
    cusgrrusgr.v
    nbcplgr
    sylan
    ralrimiva
    @3
    @18
    @12
    vv
    cV
    @3
    @20
    wa
    #
    @18
    @12
    @21
    @18
    wa
    #
    @16
    chash
    cfv
    #
    @11
    @5
    @22
    @7
    @20
    wa
    #
    @23
    @11
    wceq
    @21
    @24
    @18
    @3
    @7
    @20
    @14
    anim1i
    adantr
    @9
    cG
    cV
    cusgrrusgr.v
    hashnbusgrvd
    syl
    @18
    @21
    @23
    @17
    chash
    cfv
    #
    @5
    @16
    @17
    chash
    fveq2
    @1
    @0
    @20
    @25
    @5
    wceq
    @2
    cV
    @9
    hashdifsn
    3ad2antl2
    sylan9eqr
    eqtr3d
    ex
    ralimdva
    mpd
    @3
    @0
    @5
    cvv
    wcel
    @6
    @7
    @8
    @13
    w3a
    wb
    @0
    @1
    @2
    simp1
    @4
    c1
    cmin
    ovex
    vv
    @10
    cG
    @5
    cV
    ccusgr
    cvv
    cusgrrusgr.v
    @10
    eqid
    isrusgr0
    sylancl
    mpbir3and
end
