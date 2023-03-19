include "cusgr.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "cfv.mm"
include "cc0.mm"
include "cnbgr.mm"
include "cpr.mm"
include "cedg.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "wceq.mm"
include "cv.mm"
include "caddc.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "eqid.mm"
include "clwwlknp.mm"
include "wi.mm"
include "lsw.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sylan9eq.mm"
include "preq1d.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "a1d.mm"
include "3imp.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "nbusgreledg.mm"
include "adantr.mm"
include "mpbird.mm"

theorem clwwlknlbonbgr1
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( ( G e. USGraph /\ W e. ( N ClWWalksN G ) ) -> ( W ` ( N - 1 ) ) e. ( G NeighbVtx ( W ` 0 ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    wa
    cN
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cG
    cc0
    cW
    cfv
    #
    cnbgr
    co
    wcel
    #
    @3
    @4
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    @1
    @8
    @0
    @1
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vi
    cv
    #
    cW
    cfv
    @15
    c1
    caddc
    co
    cW
    cfv
    cpr
    @7
    wcel
    vi
    cc0
    @2
    cfzo
    co
    wral
    #
    cW
    clsw
    cfv
    #
    @4
    cpr
    #
    @7
    wcel
    #
    w3a
    @8
    vi
    @7
    cG
    cN
    @9
    cW
    @9
    eqid
    @7
    eqid
    #
    clwwlknp
    @14
    @16
    @19
    @8
    @14
    @19
    @8
    wi
    @16
    @14
    @19
    @8
    @14
    @18
    @6
    @7
    @14
    @17
    @3
    @4
    @11
    @13
    @17
    @12
    c1
    cmin
    co
    #
    cW
    cfv
    @3
    cW
    @10
    lsw
    @13
    @21
    @2
    cW
    @12
    cN
    c1
    cmin
    oveq1
    fveq2d
    sylan9eq
    preq1d
    eleq1d
    biimpd
    a1d
    3imp
    syl
    adantl
    @0
    @5
    @8
    wb
    @1
    @7
    cG
    @4
    @3
    @20
    nbusgreledg
    adantr
    mpbird
end
