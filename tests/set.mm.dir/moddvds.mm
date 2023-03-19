include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "cc0.mm"
include "crp.mm"
include "nnrp.mm"
include "adantr.mm"
include "0mod.mm"
include "syl.mm"
include "eqeq2d.mm"
include "cneg.mm"
include "caddc.mm"
include "cr.mm"
include "wi.mm"
include "zre.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "renegcld.mm"
include "modadd1.mm"
include "3expia.mm"
include "syl22anc.mm"
include "recnd.mm"
include "negsubd.mm"
include "oveq1d.mm"
include "negidd.mm"
include "eqeq12d.mm"
include "sylibd.mm"
include "resubcld.mm"
include "0red.mm"
include "npcand.mm"
include "addid2d.mm"
include "impbid.mm"
include "zsubcl.mm"
include "dvdsval3.mm"
include "sylan2.mm"
include "3bitr4d.mm"
include "3impb.mm"

theorem moddvds
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ A e. ZZ /\ B e. ZZ ) -> ( ( A mod N ) = ( B mod N ) <-> N || ( A - B ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cN
    cmo
    co
    #
    cB
    cN
    cmo
    co
    #
    wceq
    #
    cN
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    wb
    @0
    @1
    @2
    wa
    #
    wa
    #
    @6
    cN
    cmo
    co
    #
    cc0
    cN
    cmo
    co
    #
    wceq
    #
    @10
    cc0
    wceq
    #
    @5
    @7
    @9
    @11
    cc0
    @10
    @9
    cN
    crp
    wcel
    #
    @11
    cc0
    wceq
    @0
    @14
    @8
    cN
    nnrp
    adantr
    #
    cN
    0mod
    syl
    eqeq2d
    @9
    @5
    @12
    @9
    @5
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cN
    cmo
    co
    #
    cB
    @16
    caddc
    co
    #
    cN
    cmo
    co
    #
    wceq
    #
    @12
    @9
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @14
    @5
    @21
    wi
    @1
    @22
    @0
    @2
    cA
    zre
    ad2antrl
    #
    @2
    @23
    @0
    @1
    cB
    zre
    ad2antll
    #
    @9
    cB
    @26
    renegcld
    @15
    @22
    @23
    wa
    @24
    @14
    wa
    @5
    @21
    cA
    cB
    @16
    cN
    modadd1
    3expia
    syl22anc
    @9
    @18
    @10
    @20
    @11
    @9
    @17
    @6
    cN
    cmo
    @9
    cA
    cB
    @9
    cA
    @25
    recnd
    #
    @9
    cB
    @26
    recnd
    #
    negsubd
    oveq1d
    @9
    @19
    cc0
    cN
    cmo
    @9
    cB
    @28
    negidd
    oveq1d
    eqeq12d
    sylibd
    @9
    @12
    @6
    cB
    caddc
    co
    #
    cN
    cmo
    co
    #
    cc0
    cB
    caddc
    co
    #
    cN
    cmo
    co
    #
    wceq
    #
    @5
    @9
    @6
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @23
    @14
    @12
    @33
    wi
    @9
    cA
    cB
    @25
    @26
    resubcld
    @9
    0red
    @26
    @15
    @34
    @35
    wa
    @23
    @14
    wa
    @12
    @33
    @6
    cc0
    cB
    cN
    modadd1
    3expia
    syl22anc
    @9
    @30
    @3
    @32
    @4
    @9
    @29
    cA
    cN
    cmo
    @9
    cA
    cB
    @27
    @28
    npcand
    oveq1d
    @9
    @31
    cB
    cN
    cmo
    @9
    cB
    @28
    addid2d
    oveq1d
    eqeq12d
    sylibd
    impbid
    @8
    @0
    @6
    cz
    wcel
    @7
    @13
    wb
    cA
    cB
    zsubcl
    cN
    @6
    dvdsval3
    sylan2
    3bitr4d
    3impb
end
