include "cusp.mm"
include "wcel.mm"
include "ctps.mm"
include "w3a.mm"
include "cress.mm"
include "co.mm"
include "cuss.mm"
include "cfv.mm"
include "cbs.mm"
include "cust.mm"
include "crest.mm"
include "cutop.mm"
include "wceq.mm"
include "cxp.mm"
include "ressuss.mm"
include "3ad2ant3.mm"
include "wss.mm"
include "wa.mm"
include "simp1.mm"
include "eqid.mm"
include "isusp.mm"
include "sylib.mm"
include "simpld.mm"
include "ctopon.mm"
include "simp2.mm"
include "istps.mm"
include "simp3.mm"
include "toponss.mm"
include "syl2anc.mm"
include "trust.mm"
include "eqeltrd.mm"
include "ressbas2.mm"
include "syl.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "simprd.mm"
include "restutopopn.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "resstopn.mm"
include "sylanbrc.mm"

theorem ressusp
  let cA: class A
  let cB: class B
  let cJ: class J
  let cW: class W
  assume ressusp.1: |- B = ( Base ` W )
  assume ressusp.2: |- J = ( TopOpen ` W )


  assert |- ( ( W e. UnifSp /\ W e. TopSp /\ A e. J ) -> ( W |`s A ) e. UnifSp )

  proof
    cW
    cusp
    wcel
    #
    cW
    ctps
    wcel
    #
    cA
    cJ
    wcel
    #
    w3a
    #
    cW
    cA
    cress
    co
    #
    cuss
    cfv
    #
    @4
    cbs
    cfv
    #
    cust
    cfv
    #
    wcel
    cJ
    cA
    crest
    co
    #
    @5
    cutop
    cfv
    #
    wceq
    @4
    cusp
    wcel
    @3
    @5
    cA
    cust
    cfv
    #
    @7
    @3
    @5
    cW
    cuss
    cfv
    #
    cA
    cA
    cxp
    crest
    co
    #
    @10
    @2
    @0
    @5
    @12
    wceq
    @1
    cA
    cJ
    cW
    ressuss
    3ad2ant3
    #
    @3
    @11
    cB
    cust
    cfv
    wcel
    #
    cA
    cB
    wss
    #
    @12
    @10
    wcel
    @3
    @14
    cJ
    @11
    cutop
    cfv
    #
    wceq
    #
    @3
    @0
    @14
    @17
    wa
    @0
    @1
    @2
    simp1
    cB
    @11
    cJ
    cW
    ressusp.1
    @11
    eqid
    ressusp.2
    isusp
    sylib
    #
    simpld
    #
    @3
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @2
    @15
    @3
    @1
    @20
    @0
    @1
    @2
    simp2
    cB
    cJ
    cW
    ressusp.1
    ressusp.2
    istps
    sylib
    @0
    @1
    @2
    simp3
    #
    cA
    cJ
    cB
    toponss
    syl2anc
    #
    cA
    @11
    cB
    trust
    syl2anc
    eqeltrd
    @3
    cA
    @6
    cust
    @3
    @15
    cA
    @6
    wceq
    @22
    cA
    cB
    @4
    cW
    @4
    eqid
    #
    ressusp.1
    ressbas2
    syl
    fveq2d
    eleqtrd
    @3
    @16
    cA
    crest
    co
    #
    @12
    cutop
    cfv
    #
    @8
    @9
    @3
    @14
    cA
    @16
    wcel
    @24
    @25
    wceq
    @19
    @3
    cA
    cJ
    @16
    @21
    @3
    @14
    @17
    @18
    simprd
    #
    eleqtrd
    cA
    @11
    cB
    restutopopn
    syl2anc
    @3
    cJ
    @16
    cA
    crest
    @26
    oveq1d
    @3
    @5
    @12
    cutop
    @13
    fveq2d
    3eqtr4d
    @6
    @5
    @8
    @4
    @6
    eqid
    @5
    eqid
    cA
    @4
    cJ
    cW
    @23
    ressusp.2
    resstopn
    isusp
    sylanbrc
end
