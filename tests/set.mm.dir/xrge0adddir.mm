include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cico.mm"
include "cxad.mm"
include "cxmu.mm"
include "wceq.mm"
include "wa.mm"
include "cxr.mm"
include "cr.mm"
include "iccssxr.mm"
include "simpl1.mm"
include "sseldi.mm"
include "simpl2.mm"
include "rge0ssre.mm"
include "simpr.mm"
include "xadddir.mm"
include "syl3anc.mm"
include "clt.mm"
include "wbr.mm"
include "simpll1.mm"
include "simpll2.mm"
include "xaddcld.mm"
include "xrge0addgt0.mm"
include "syl21anc.mm"
include "xmulpnf1.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "ad2antlr.mm"
include "cmnf.mm"
include "wne.mm"
include "simpll3.mm"
include "ge0xmulcl.mm"
include "xrge0neqmnf.mm"
include "syl.mm"
include "xaddpnf2.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "xmul02.mm"
include "oveq1.mm"
include "adantl.mm"
include "xmulcld.mm"
include "xaddid2.mm"
include "3eqtr3d.mm"
include "3eqtr2rd.mm"
include "cle.mm"
include "wo.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "xrleloe.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "wb.mm"
include "0lepnf.mm"
include "eliccelico.mm"
include "mp3an.mm"
include "3anbi3i.mm"
include "simp3bi.mm"

theorem xrge0adddir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ C e. ( 0 [,] +oo ) ) -> ( ( A +e B ) *e C ) = ( ( A *e C ) +e ( B *e C ) ) )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cC
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    cA
    cB
    cxad
    co
    #
    cC
    cxmu
    co
    #
    cA
    cC
    cxmu
    co
    #
    cB
    cC
    cxmu
    co
    #
    cxad
    co
    #
    wceq
    #
    cC
    cpnf
    wceq
    #
    @4
    @6
    wa
    #
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cr
    wcel
    @12
    @14
    @0
    cxr
    cA
    cc0
    cpnf
    iccssxr
    #
    @1
    @2
    @3
    @6
    simpl1
    sseldi
    @14
    @0
    cxr
    cB
    @17
    @1
    @2
    @3
    @6
    simpl2
    sseldi
    @14
    @5
    cr
    cC
    rge0ssre
    @4
    @6
    simpr
    sseldi
    cA
    cB
    cC
    xadddir
    syl3anc
    @4
    @13
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    @12
    cc0
    cA
    wceq
    #
    @18
    @19
    wa
    #
    @8
    cpnf
    @10
    cxad
    co
    #
    @11
    @21
    @7
    cpnf
    cxmu
    co
    #
    cpnf
    @8
    @22
    @21
    @7
    cxr
    wcel
    cc0
    @7
    clt
    wbr
    #
    @23
    cpnf
    wceq
    @21
    cA
    cB
    @21
    @0
    cxr
    cA
    @17
    @1
    @2
    @3
    @13
    @19
    simpll1
    #
    sseldi
    #
    @21
    @0
    cxr
    cB
    @17
    @1
    @2
    @3
    @13
    @19
    simpll2
    #
    sseldi
    xaddcld
    @21
    @1
    @2
    @19
    @24
    @25
    @27
    @18
    @19
    simpr
    #
    cA
    cB
    xrge0addgt0
    syl21anc
    @7
    xmulpnf1
    syl2anc
    @13
    @8
    @23
    wceq
    @4
    @19
    cC
    cpnf
    @7
    cxmu
    oveq2
    ad2antlr
    @21
    @10
    cxr
    wcel
    #
    @10
    cmnf
    wne
    #
    @22
    cpnf
    wceq
    @21
    @0
    cxr
    @10
    @17
    @21
    @2
    @3
    @10
    @0
    wcel
    #
    @27
    @1
    @2
    @3
    @13
    @19
    simpll3
    cB
    cC
    ge0xmulcl
    syl2anc
    #
    sseldi
    @21
    @31
    @30
    @32
    @10
    xrge0neqmnf
    syl
    @10
    xaddpnf2
    syl2anc
    3eqtr4d
    @21
    @9
    cpnf
    @10
    cxad
    @21
    @9
    cA
    cpnf
    cxmu
    co
    #
    cpnf
    @13
    @9
    @33
    wceq
    @4
    @19
    cC
    cpnf
    cA
    cxmu
    oveq2
    ad2antlr
    @21
    @15
    @19
    @33
    cpnf
    wceq
    @26
    @28
    cA
    xmulpnf1
    syl2anc
    eqtrd
    oveq1d
    eqtr4d
    @18
    @20
    wa
    #
    @11
    @10
    cc0
    cB
    cxad
    co
    #
    cC
    cxmu
    co
    #
    @8
    @34
    cc0
    cC
    cxmu
    co
    #
    @10
    cxad
    co
    cc0
    @10
    cxad
    co
    #
    @11
    @10
    @34
    @37
    cc0
    @10
    cxad
    @34
    cC
    cxr
    wcel
    @37
    cc0
    wceq
    @34
    @0
    cxr
    cC
    @17
    @1
    @2
    @3
    @13
    @20
    simpll3
    sseldi
    #
    cC
    xmul02
    syl
    oveq1d
    @34
    @37
    @9
    @10
    cxad
    @20
    @37
    @9
    wceq
    @18
    cc0
    cA
    cC
    cxmu
    oveq1
    adantl
    oveq1d
    @34
    @29
    @38
    @10
    wceq
    @34
    cB
    cC
    @34
    @0
    cxr
    cB
    @17
    @1
    @2
    @3
    @13
    @20
    simpll2
    sseldi
    #
    @39
    xmulcld
    @10
    xaddid2
    syl
    3eqtr3d
    @34
    @35
    cB
    cC
    cxmu
    @34
    @16
    @35
    cB
    wceq
    @40
    cB
    xaddid2
    syl
    oveq1d
    @20
    @36
    @8
    wceq
    @18
    @20
    @35
    @7
    cC
    cxmu
    cc0
    cA
    cB
    cxad
    oveq1
    oveq1d
    adantl
    3eqtr2rd
    @18
    cc0
    cxr
    wcel
    #
    @15
    cc0
    cA
    cle
    wbr
    #
    @19
    @20
    wo
    #
    @41
    @18
    0xr
    a1i
    #
    @18
    @0
    cxr
    cA
    @17
    @1
    @2
    @3
    @13
    simpl1
    #
    sseldi
    @18
    @41
    cpnf
    cxr
    wcel
    #
    @1
    @42
    @44
    @46
    @18
    pnfxr
    a1i
    @45
    cc0
    cpnf
    cA
    iccgelb
    syl3anc
    @41
    @15
    wa
    @42
    @43
    cc0
    cA
    xrleloe
    biimpa
    syl21anc
    mpjaodan
    @4
    @1
    @2
    @6
    @13
    wo
    #
    @3
    @47
    @1
    @2
    @41
    @46
    cc0
    cpnf
    cle
    wbr
    @3
    @47
    wb
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    cC
    eliccelico
    mp3an
    3anbi3i
    simp3bi
    mpjaodan
end
