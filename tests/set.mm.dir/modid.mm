include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "wceq.mm"
include "modval.mm"
include "adantr.mm"
include "caddc.mm"
include "cc.mm"
include "rerpdivcl.mm"
include "recnd.mm"
include "addid2.mm"
include "fveq2d.mm"
include "syl.mm"
include "c1.mm"
include "rpregt0.mm"
include "divge0.mm"
include "sylan2.mm"
include "an32s.mm"
include "adantrr.mm"
include "simpr.mm"
include "rpcn.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "ad2ant2l.mm"
include "wb.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "1re.mm"
include "ltdivmul.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "cz.mm"
include "0z.mm"
include "flbi2.mm"
include "sylancr.mm"
include "mpbir2and.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "recn.mm"
include "subid1d.mm"
include "ad2antrr.mm"

theorem modid
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR+ ) /\ ( 0 <_ A /\ A < B ) ) -> ( A mod B ) = A )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cmo
    co
    #
    cA
    cB
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cA
    @2
    @7
    @11
    wceq
    @5
    cA
    cB
    modval
    adantr
    @6
    @11
    cA
    cc0
    cmin
    co
    #
    cA
    @6
    @10
    cc0
    cA
    cmin
    @6
    @10
    cB
    cc0
    cmul
    co
    #
    cc0
    @6
    @9
    cc0
    cB
    cmul
    @6
    cc0
    @8
    caddc
    co
    #
    cfl
    cfv
    #
    @9
    cc0
    @6
    @8
    cc
    wcel
    #
    @15
    @9
    wceq
    @6
    @8
    @2
    @8
    cr
    wcel
    #
    @5
    cA
    cB
    rerpdivcl
    adantr
    #
    recnd
    @16
    @14
    @8
    cfl
    @8
    addid2
    fveq2d
    syl
    @6
    @15
    cc0
    wceq
    #
    cc0
    @8
    cle
    wbr
    #
    @8
    c1
    clt
    wbr
    #
    @2
    @3
    @20
    @4
    @0
    @3
    @1
    @20
    @1
    @0
    @3
    wa
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    #
    @20
    cB
    rpregt0
    #
    cA
    cB
    divge0
    sylan2
    an32s
    adantrr
    @6
    @21
    cA
    cB
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @4
    @25
    @0
    @3
    @1
    @4
    wa
    cA
    cB
    @24
    clt
    @1
    @4
    simpr
    @1
    @24
    cB
    wceq
    @4
    @1
    cB
    cB
    rpcn
    #
    mulid1d
    adantr
    breqtrrd
    ad2ant2l
    @6
    @0
    @22
    @21
    @25
    wb
    #
    @0
    @1
    @5
    simpll
    @1
    @22
    @0
    @5
    @23
    ad2antlr
    @0
    c1
    cr
    wcel
    @22
    @27
    1re
    cA
    c1
    cB
    ltdivmul
    mp3an2
    syl2anc
    mpbird
    @6
    cc0
    cz
    wcel
    @17
    @19
    @20
    @21
    wa
    wb
    0z
    @18
    @8
    cc0
    flbi2
    sylancr
    mpbir2and
    eqtr3d
    oveq2d
    @1
    @13
    cc0
    wceq
    @0
    @5
    @1
    cB
    @26
    mul01d
    ad2antlr
    eqtrd
    oveq2d
    @0
    @12
    cA
    wceq
    @1
    @5
    @0
    cA
    cA
    recn
    subid1d
    ad2antrr
    eqtrd
    eqtrd
end
