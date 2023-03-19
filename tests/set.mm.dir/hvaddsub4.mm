include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "cmv.mm"
include "wceq.mm"
include "wb.mm"
include "hvaddcl.mm"
include "adantr.mm"
include "adantl.mm"
include "ancoms.mm"
include "ad2ant2lr.mm"
include "hvsubcan2.mm"
include "syl3anc.mm"
include "c0v.mm"
include "simpr.mm"
include "anim2i.mm"
include "hvsub4.mm"
include "syldan.mm"
include "hvsubid.mm"
include "ad2antlr.mm"
include "oveq2d.mm"
include "hvsubcl.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "adantlr.mm"
include "3eqtrd.mm"
include "adantrr.mm"
include "simpl.mm"
include "anim1i.mm"
include "ad2antrr.mm"
include "oveq1d.mm"
include "hvaddid2.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem hvaddsub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( A +h B ) = ( C +h D ) <-> ( A -h C ) = ( D -h B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cva
    co
    #
    cC
    cB
    cva
    co
    #
    cmv
    co
    #
    cC
    cD
    cva
    co
    #
    @8
    cmv
    co
    #
    wceq
    #
    @7
    @10
    wceq
    #
    cA
    cC
    cmv
    co
    #
    cD
    cB
    cmv
    co
    #
    wceq
    @6
    @7
    chil
    wcel
    #
    @10
    chil
    wcel
    #
    @8
    chil
    wcel
    #
    @12
    @13
    wb
    @2
    @16
    @5
    cA
    cB
    hvaddcl
    adantr
    @5
    @17
    @2
    cC
    cD
    hvaddcl
    adantl
    @1
    @3
    @18
    @0
    @4
    @3
    @1
    @18
    cC
    cB
    hvaddcl
    ancoms
    ad2ant2lr
    @7
    @10
    @8
    hvsubcan2
    syl3anc
    @6
    @9
    @14
    @11
    @15
    @2
    @3
    @9
    @14
    wceq
    @4
    @2
    @3
    wa
    #
    @9
    @14
    cB
    cB
    cmv
    co
    #
    cva
    co
    #
    @14
    c0v
    cva
    co
    #
    @14
    @2
    @3
    @3
    @1
    wa
    #
    @9
    @21
    wceq
    @3
    @2
    @23
    @2
    @1
    @3
    @0
    @1
    simpr
    anim2i
    ancoms
    cA
    cB
    cC
    cB
    hvsub4
    syldan
    @19
    @20
    c0v
    @14
    cva
    @1
    @20
    c0v
    wceq
    @0
    @3
    cB
    hvsubid
    ad2antlr
    oveq2d
    @0
    @3
    @22
    @14
    wceq
    #
    @1
    @0
    @3
    wa
    @14
    chil
    wcel
    @24
    cA
    cC
    hvsubcl
    @14
    ax-hvaddid
    syl
    adantlr
    3eqtrd
    adantrr
    @1
    @5
    @11
    @15
    wceq
    #
    @0
    @5
    @1
    @25
    @5
    @1
    wa
    #
    @11
    cC
    cC
    cmv
    co
    #
    @15
    cva
    co
    #
    c0v
    @15
    cva
    co
    #
    @15
    @5
    @1
    @23
    @11
    @28
    wceq
    @5
    @3
    @1
    @3
    @4
    simpl
    anim1i
    cC
    cD
    cC
    cB
    hvsub4
    syldan
    @26
    @27
    c0v
    @15
    cva
    @3
    @27
    c0v
    wceq
    @4
    @1
    cC
    hvsubid
    ad2antrr
    oveq1d
    @4
    @1
    @29
    @15
    wceq
    #
    @3
    @4
    @1
    wa
    @15
    chil
    wcel
    @30
    cD
    cB
    hvsubcl
    @15
    hvaddid2
    syl
    adantll
    3eqtrd
    ancoms
    adantll
    eqeq12d
    bitr3d
end
