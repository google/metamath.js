include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cply.mm"
include "cfv.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdgr.mm"
include "wceq.mm"
include "c0p.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "eqeq12d.mm"
include "wa.mm"
include "caddc.mm"
include "wss.mm"
include "ssid.mm"
include "simpl1.mm"
include "plyconst.mm"
include "sylancr.mm"
include "0cn.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "simpl2.mm"
include "eqnetrd.mm"
include "ne0p.mm"
include "plyssc.mm"
include "simpl3.mm"
include "sseldi.mm"
include "simpr.mm"
include "eqid.mm"
include "dgrmul.mm"
include "syl22anc.mm"
include "0dgr.mm"
include "syl.mm"
include "oveq1d.mm"
include "cn0.mm"
include "dgrcl.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "simp1.mm"
include "ofc12.mm"
include "mul01d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtrd.mm"
include "df-0p.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "pm2.61ne.mm"

theorem dgrmulc
  let cA: class A
  let cS: class S
  let cF: class F


  assert |- ( ( A e. CC /\ A =/= 0 /\ F e. ( Poly ` S ) ) -> ( deg ` ( ( CC X. { A } ) oF x. F ) ) = ( deg ` F ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    w3a
    #
    cc
    cA
    csn
    cxp
    #
    cF
    cmul
    cof
    #
    co
    #
    cdgr
    cfv
    #
    cF
    cdgr
    cfv
    #
    wceq
    @5
    c0p
    @6
    co
    #
    cdgr
    cfv
    #
    cc0
    wceq
    cF
    c0p
    cF
    c0p
    wceq
    #
    @8
    @11
    @9
    cc0
    @12
    @7
    @10
    cdgr
    cF
    c0p
    @5
    @6
    oveq2
    fveq2d
    @12
    @9
    c0p
    cdgr
    cfv
    #
    cc0
    cF
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    eqeq12d
    @4
    cF
    c0p
    wne
    #
    wa
    #
    @8
    @5
    cdgr
    cfv
    #
    @9
    caddc
    co
    #
    cc0
    @9
    caddc
    co
    @9
    @15
    @5
    cc
    cply
    cfv
    #
    wcel
    #
    @5
    c0p
    wne
    #
    cF
    @18
    wcel
    @14
    @8
    @17
    wceq
    @15
    cc
    cc
    wss
    @0
    @19
    cc
    ssid
    @0
    @1
    @3
    @14
    simpl1
    #
    cA
    cc
    plyconst
    sylancr
    @15
    cc0
    cc
    wcel
    #
    cc0
    @5
    cfv
    #
    cc0
    wne
    @20
    0cn
    @15
    @23
    cA
    cc0
    @15
    @0
    @22
    @23
    cA
    wceq
    @21
    0cn
    cc
    cA
    cc0
    cc
    fvconst2g
    sylancl
    @0
    @1
    @3
    @14
    simpl2
    eqnetrd
    cc0
    @5
    ne0p
    sylancr
    @15
    @2
    @18
    cF
    cS
    plyssc
    @0
    @1
    @3
    @14
    simpl3
    #
    sseldi
    @4
    @14
    simpr
    cc
    @5
    cF
    @16
    @9
    @16
    eqid
    @9
    eqid
    dgrmul
    syl22anc
    @15
    @16
    cc0
    @9
    caddc
    @15
    @0
    @16
    cc0
    wceq
    @21
    cA
    0dgr
    syl
    oveq1d
    @15
    @9
    @15
    @9
    @15
    @3
    @9
    cn0
    wcel
    @24
    cS
    cF
    dgrcl
    syl
    nn0cnd
    addid2d
    3eqtrd
    @4
    @11
    @13
    cc0
    @4
    @10
    c0p
    cdgr
    @4
    @5
    cc
    cc0
    csn
    #
    cxp
    #
    @6
    co
    #
    @26
    @10
    c0p
    @4
    @27
    cc
    cA
    cc0
    cmul
    co
    #
    csn
    #
    cxp
    @26
    @4
    cc
    cA
    cc0
    cmul
    cvv
    cc
    cc
    cc
    cvv
    wcel
    @4
    cnex
    a1i
    @0
    @1
    @3
    simp1
    #
    @22
    @4
    0cn
    a1i
    ofc12
    @4
    @29
    @25
    cc
    @4
    @28
    cc0
    @4
    cA
    @30
    mul01d
    sneqd
    xpeq2d
    eqtrd
    c0p
    @26
    @5
    @6
    df-0p
    oveq2i
    df-0p
    3eqtr4g
    fveq2d
    dgr0
    syl6eq
    pm2.61ne
end
