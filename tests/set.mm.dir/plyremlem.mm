include "cc.mm"
include "wcel.mm"
include "cply.mm"
include "cfv.mm"
include "cdgr.mm"
include "c1.mm"
include "wceq.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "cidp.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "wss.mm"
include "ssid.mm"
include "ax-1cn.mm"
include "plyid.mm"
include "mp2an.mm"
include "plyconst.mm"
include "mpan.mm"
include "plysubcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "cneg.mm"
include "caddc.mm"
include "cv.mm"
include "cmpt.mm"
include "wa.mm"
include "negcl.mm"
include "addcom.mm"
include "sylan.mm"
include "negsub.mm"
include "ancoms.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "negex.mm"
include "simpr.mm"
include "fconstmpt.mm"
include "cid.mm"
include "cres.mm"
include "df-idp.mm"
include "mptresid.mm"
include "eqtr4i.mm"
include "offval2.mm"
include "simpl.mm"
include "3eqtr4d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "clt.mm"
include "wbr.mm"
include "0dgr.mm"
include "syl.mm"
include "0lt1.mm"
include "syl6eqbr.mm"
include "eqid.mm"
include "dgrid.mm"
include "eqcomi.mm"
include "dgradd2.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "adantr.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "eqeq1d.mm"
include "wb.mm"
include "subeq0.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "wf.mm"
include "wfn.mm"
include "plyf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "4syl.mm"
include "eleq1a.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "3jca.mm"

theorem plyremlem
  let cA: class A
  let cG: class G
  let vz: setvar z
  let cF: class F
  let cS: class S
  assume plyrem.1: |- G = ( Xp oF - ( CC X. { A } ) )


  assert |- ( A e. CC -> ( G e. ( Poly ` CC ) /\ ( deg ` G ) = 1 /\ ( `' G " { 0 } ) = { A } ) )

  proof
    cA
    cc
    wcel
    #
    cG
    cc
    cply
    cfv
    #
    wcel
    #
    cG
    cdgr
    cfv
    #
    c1
    wceq
    cG
    ccnv
    cc0
    csn
    cima
    #
    cA
    csn
    #
    wceq
    @0
    cG
    cidp
    cc
    @5
    cxp
    #
    cmin
    cof
    co
    #
    @1
    plyrem.1
    @0
    cidp
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    @7
    @1
    wcel
    cc
    cc
    wss
    #
    c1
    cc
    wcel
    @8
    cc
    ssid
    #
    ax-1cn
    cc
    plyid
    mp2an
    #
    @10
    @0
    @9
    @11
    cA
    cc
    plyconst
    mpan
    cc
    cidp
    @6
    plysubcl
    sylancr
    syl5eqel
    #
    @0
    cc
    cA
    cneg
    #
    csn
    cxp
    #
    cidp
    caddc
    cof
    co
    #
    cdgr
    cfv
    #
    @3
    c1
    @0
    @16
    cG
    cdgr
    @0
    @16
    @7
    cG
    @0
    vz
    cc
    @14
    vz
    cv
    #
    caddc
    co
    #
    cmpt
    vz
    cc
    @18
    cA
    cmin
    co
    #
    cmpt
    #
    @16
    @7
    @0
    vz
    cc
    @19
    @20
    @0
    @18
    cc
    wcel
    #
    wa
    #
    @19
    @18
    @14
    caddc
    co
    #
    @20
    @0
    @14
    cc
    wcel
    #
    @22
    @19
    @24
    wceq
    cA
    negcl
    #
    @14
    @18
    addcom
    sylan
    @22
    @0
    @24
    @20
    wceq
    @18
    cA
    negsub
    ancoms
    eqtrd
    mpteq2dva
    @0
    vz
    cc
    @14
    @18
    caddc
    @15
    cidp
    cvv
    cvv
    cc
    cc
    cvv
    wcel
    @0
    cnex
    a1i
    #
    @14
    cvv
    wcel
    @23
    cA
    negex
    a1i
    @0
    @22
    simpr
    #
    @15
    vz
    cc
    @14
    cmpt
    wceq
    @0
    vz
    cc
    @14
    fconstmpt
    a1i
    cidp
    vz
    cc
    @18
    cmpt
    #
    wceq
    @0
    cidp
    cid
    cc
    cres
    @29
    df-idp
    vz
    cc
    mptresid
    eqtr4i
    a1i
    #
    offval2
    @0
    vz
    cc
    @18
    cA
    cmin
    cidp
    @6
    cvv
    cc
    cc
    @27
    @28
    @0
    @22
    simpl
    @30
    @6
    vz
    cc
    cA
    cmpt
    wceq
    @0
    vz
    cc
    cA
    fconstmpt
    a1i
    offval2
    #
    3eqtr4d
    plyrem.1
    syl6eqr
    fveq2d
    @0
    @15
    @1
    wcel
    #
    @8
    @15
    cdgr
    cfv
    #
    c1
    clt
    wbr
    @17
    c1
    wceq
    @0
    @10
    @25
    @32
    @11
    @26
    @14
    cc
    plyconst
    sylancr
    @8
    @0
    @12
    a1i
    @0
    @33
    cc0
    c1
    clt
    @0
    @25
    @33
    cc0
    wceq
    @26
    @14
    0dgr
    syl
    0lt1
    syl6eqbr
    cc
    @15
    cidp
    @33
    c1
    @33
    eqid
    cidp
    cdgr
    cfv
    c1
    dgrid
    eqcomi
    dgradd2
    syl3anc
    eqtr3d
    @0
    vz
    @4
    @5
    @0
    @18
    @4
    wcel
    #
    @18
    cA
    wceq
    #
    @18
    @5
    wcel
    @0
    @22
    @18
    cG
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @22
    @35
    wa
    @34
    @35
    @0
    @22
    @37
    @35
    @23
    @37
    @20
    cc0
    wceq
    #
    @35
    @23
    @36
    @20
    cc0
    @23
    @36
    @18
    @21
    cfv
    #
    @20
    @0
    @36
    @40
    wceq
    @22
    @0
    @18
    cG
    @21
    @0
    cG
    @7
    @21
    plyrem.1
    @31
    syl5eq
    fveq1d
    adantr
    @23
    @22
    @20
    cvv
    wcel
    @40
    @20
    wceq
    @28
    @18
    cA
    cmin
    ovex
    vz
    cc
    @20
    cvv
    @21
    @21
    eqid
    fvmpt2
    sylancl
    eqtrd
    eqeq1d
    @22
    @0
    @39
    @35
    wb
    @18
    cA
    subeq0
    ancoms
    bitrd
    pm5.32da
    @0
    @2
    cc
    cc
    cG
    wf
    cG
    cc
    wfn
    @34
    @38
    wb
    @13
    cc
    cG
    plyf
    cc
    cc
    cG
    ffn
    cc
    cc0
    @18
    cG
    fniniseg
    4syl
    @0
    @35
    @22
    cA
    cc
    @18
    eleq1a
    pm4.71rd
    3bitr4d
    vz
    cA
    velsn
    syl6bbr
    eqrdv
    3jca
end
