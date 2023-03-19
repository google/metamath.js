include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "wrex.mm"
include "wb.mm"
include "nnz.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "divides.mm"
include "syl2anc.mm"
include "simp2.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "syl6bbr.mm"
include "wi.mm"
include "cc.mm"
include "gcdcl.mm"
include "nn0cnd.mm"
include "3adant3.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan4d.mm"
include "cn0.mm"
include "nnnn0.mm"
include "mulgcdr.mm"
include "syl3an3.mm"
include "oveq1d.mm"
include "zcn.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "oveq12.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "3expa.mm"
include "expcom.mm"
include "rexlimdvv.mm"
include "sylbid.mm"
include "imp.mm"

theorem gcddiv
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. NN ) /\ ( C || A /\ C || B ) ) -> ( ( A gcd B ) / C ) = ( ( A / C ) gcd ( B / C ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cC
    cA
    cdvds
    wbr
    #
    cC
    cB
    cdvds
    wbr
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    cC
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    cgcd
    co
    #
    wceq
    #
    @3
    @6
    va
    cv
    #
    cC
    cmul
    co
    #
    cA
    wceq
    #
    vb
    cv
    #
    cC
    cmul
    co
    #
    cB
    wceq
    #
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    @12
    @3
    @6
    @15
    va
    cz
    wrex
    #
    @18
    vb
    cz
    wrex
    #
    wa
    @20
    @3
    @4
    @21
    @5
    @22
    @3
    cC
    cz
    wcel
    #
    @0
    @4
    @21
    wb
    @2
    @0
    @23
    @1
    cC
    nnz
    3ad2ant3
    #
    @0
    @1
    @2
    simp1
    va
    cC
    cA
    divides
    syl2anc
    @3
    @23
    @1
    @5
    @22
    wb
    @24
    @0
    @1
    @2
    simp2
    vb
    cC
    cB
    divides
    syl2anc
    anbi12d
    @15
    @18
    va
    vb
    cz
    cz
    reeanv
    syl6bbr
    @2
    @0
    @20
    @12
    wi
    @1
    @2
    @19
    @12
    va
    vb
    cz
    cz
    @13
    cz
    wcel
    #
    @16
    cz
    wcel
    #
    wa
    #
    @2
    @19
    @12
    wi
    #
    @25
    @26
    @2
    @28
    @25
    @26
    @2
    w3a
    #
    @14
    @17
    cgcd
    co
    #
    cC
    cdiv
    co
    #
    @14
    cC
    cdiv
    co
    #
    @17
    cC
    cdiv
    co
    #
    cgcd
    co
    #
    wceq
    @19
    @12
    @29
    @13
    @16
    cgcd
    co
    #
    cC
    cmul
    co
    #
    cC
    cdiv
    co
    @35
    @31
    @34
    @29
    @35
    cC
    @25
    @26
    @35
    cc
    wcel
    @2
    @27
    @35
    @13
    @16
    gcdcl
    nn0cnd
    3adant3
    @2
    @25
    cC
    cc
    wcel
    @26
    cC
    nncn
    3ad2ant3
    #
    @2
    @25
    cC
    cc0
    wne
    @26
    cC
    nnne0
    3ad2ant3
    #
    divcan4d
    @29
    @30
    @36
    cC
    cdiv
    @2
    @25
    @26
    cC
    cn0
    wcel
    @30
    @36
    wceq
    cC
    nnnn0
    @13
    @16
    cC
    mulgcdr
    syl3an3
    oveq1d
    @29
    @32
    @13
    @33
    @16
    cgcd
    @29
    @13
    cC
    @25
    @26
    @13
    cc
    wcel
    @2
    @13
    zcn
    3ad2ant1
    @37
    @38
    divcan4d
    @29
    @16
    cC
    @26
    @25
    @16
    cc
    wcel
    @2
    @16
    zcn
    3ad2ant2
    @37
    @38
    divcan4d
    oveq12d
    3eqtr4d
    @19
    @31
    @8
    @34
    @11
    @19
    @30
    @7
    cC
    cdiv
    @14
    cA
    @17
    cB
    cgcd
    oveq12
    oveq1d
    @15
    @18
    @32
    @9
    @33
    @10
    cgcd
    @14
    cA
    cC
    cdiv
    oveq1
    @17
    cB
    cC
    cdiv
    oveq1
    oveqan12d
    eqeq12d
    syl5ibcom
    3expa
    expcom
    rexlimdvv
    3ad2ant3
    sylbid
    imp
end
