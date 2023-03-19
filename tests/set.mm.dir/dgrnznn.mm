include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "wceq.mm"
include "cdgr.mm"
include "wn.mm"
include "cn.mm"
include "wo.mm"
include "csn.mm"
include "cxp.mm"
include "simpr.mm"
include "fveq1d.mm"
include "simplr.mm"
include "fvex.mm"
include "fvconst2.mm"
include "ad2antrr.mm"
include "3eqtr3rd.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtrd.mm"
include "df-0p.mm"
include "syl6eqr.mm"
include "ex.mm"
include "necon3ad.mm"
include "impcom.mm"
include "adantll.mm"
include "wb.mm"
include "0dgrb.mm"
include "mtbird.mm"
include "cn0.mm"
include "dgrcl.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel2.mm"
include "sylc.mm"

theorem dgrnznn
  let cA: class A
  let cP: class P
  let cS: class S


  assert |- ( ( ( P e. ( Poly ` S ) /\ P =/= 0p ) /\ ( A e. CC /\ ( P ` A ) = 0 ) ) -> ( deg ` P ) e. NN )

  proof
    cP
    cS
    cply
    cfv
    wcel
    #
    cP
    c0p
    wne
    #
    wa
    cA
    cc
    wcel
    #
    cA
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    wa
    #
    cP
    cdgr
    cfv
    #
    cc0
    wceq
    #
    wn
    @7
    cn
    wcel
    #
    @8
    wo
    #
    @9
    @6
    @8
    cP
    cc
    cc0
    cP
    cfv
    #
    csn
    #
    cxp
    #
    wceq
    #
    @1
    @5
    @14
    wn
    #
    @0
    @5
    @1
    @15
    @5
    @14
    cP
    c0p
    @5
    @14
    cP
    c0p
    wceq
    @5
    @14
    wa
    #
    cP
    cc
    cc0
    csn
    #
    cxp
    #
    c0p
    @16
    cP
    @13
    @18
    @5
    @14
    simpr
    #
    @16
    @12
    @17
    cc
    @16
    @11
    cc0
    @16
    @3
    cA
    @13
    cfv
    #
    cc0
    @11
    @16
    cA
    cP
    @13
    @19
    fveq1d
    @2
    @4
    @14
    simplr
    @2
    @20
    @11
    wceq
    @4
    @14
    cc
    @11
    cA
    cc0
    cP
    fvex
    fvconst2
    ad2antrr
    3eqtr3rd
    sneqd
    xpeq2d
    eqtrd
    df-0p
    syl6eqr
    ex
    necon3ad
    impcom
    adantll
    @0
    @8
    @14
    wb
    @1
    @5
    cS
    cP
    0dgrb
    ad2antrr
    mtbird
    @6
    @7
    cn0
    wcel
    #
    @10
    @0
    @21
    @1
    @5
    cS
    cP
    dgrcl
    ad2antrr
    @7
    elnn0
    sylib
    @8
    @9
    orel2
    sylc
end
