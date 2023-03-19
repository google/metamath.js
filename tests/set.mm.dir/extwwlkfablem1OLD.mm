include "cusgr.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "c1.mm"
include "cnbgr.mm"
include "cpr.mm"
include "cedg.mm"
include "preq1.mm"
include "3ad2ant3.mm"
include "prcom.mm"
include "syl6eq.mm"
include "caddc.mm"
include "1e2m1.mm"
include "oveq2i.mm"
include "eluzelcn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "syl5req.mm"
include "fveq2d.mm"
include "preq2d.mm"
include "adantr.mm"
include "cfzo.mm"
include "cv.mm"
include "wral.mm"
include "ige2m2fzo.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "clsw.mm"
include "eqid.mm"
include "clwwlknp.mm"
include "simp2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2an.mm"
include "eqeltrrd.mm"
include "adantll.mm"
include "3adant3.mm"
include "wb.mm"
include "nbusgreledg.mm"
include "3ad2ant1.mm"
include "mpbird.mm"

theorem extwwlkfablem1OLD
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( ( ( G e. USGraph /\ N e. ( ZZ>= ` 2 ) ) /\ W e. ( N ClWWalksN G ) /\ ( W ` ( N - 2 ) ) = ( W ` 0 ) ) -> ( W ` ( N - 1 ) ) e. ( G NeighbVtx ( W ` 0 ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wa
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cN
    c2
    cmin
    co
    #
    cW
    cfv
    #
    cc0
    cW
    cfv
    #
    wceq
    #
    w3a
    #
    cN
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cG
    @6
    cnbgr
    co
    wcel
    #
    @10
    @6
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    @8
    @5
    @10
    cpr
    #
    @12
    @13
    @8
    @15
    @6
    @10
    cpr
    #
    @12
    @7
    @2
    @15
    @16
    wceq
    @3
    @5
    @6
    @10
    preq1
    3ad2ant3
    @6
    @10
    prcom
    syl6eq
    @2
    @3
    @15
    @13
    wcel
    #
    @7
    @1
    @3
    @17
    @0
    @1
    @3
    wa
    @5
    @4
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    @15
    @13
    @1
    @20
    @15
    wceq
    @3
    @1
    @19
    @10
    @5
    @1
    @18
    @9
    cW
    @1
    @9
    cN
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @18
    c1
    @21
    cN
    cmin
    1e2m1
    oveq2i
    @1
    cN
    c2
    c1
    c2
    cN
    eluzelcn
    @1
    2cnd
    @1
    1cnd
    subsubd
    syl5req
    fveq2d
    preq2d
    adantr
    @1
    @4
    cc0
    @9
    cfzo
    co
    #
    wcel
    vi
    cv
    #
    cW
    cfv
    #
    @23
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    @13
    wcel
    #
    vi
    @22
    wral
    #
    @20
    @13
    wcel
    #
    @3
    cN
    ige2m2fzo
    @3
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    cW
    chash
    cfv
    cN
    wceq
    wa
    @29
    cW
    clsw
    cfv
    @6
    cpr
    @13
    wcel
    vi
    @13
    cG
    cN
    @31
    cW
    @31
    eqid
    @13
    eqid
    #
    clwwlknp
    simp2d
    @28
    @30
    vi
    @4
    @22
    @23
    @4
    wceq
    #
    @27
    @20
    @13
    @33
    @24
    @5
    @26
    @19
    @23
    @4
    cW
    fveq2
    @33
    @25
    @18
    cW
    @23
    @4
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    rspcva
    syl2an
    eqeltrrd
    adantll
    3adant3
    eqeltrrd
    @2
    @3
    @11
    @14
    wb
    #
    @7
    @0
    @34
    @1
    @13
    cG
    @6
    @10
    @32
    nbusgreledg
    adantr
    3ad2ant1
    mpbird
end
