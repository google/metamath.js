include "cn.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "cgcd.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wa.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "cprime.mm"
include "wnel.mm"
include "wb.mm"
include "ncoprmgcdgt1b.mm"
include "bicomd.mm"
include "3adant3.mm"
include "wn.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "wo.mm"
include "cle.mm"
include "wi.mm"
include "cz.mm"
include "simp1.mm"
include "eluzelz.mm"
include "anim12ci.mm"
include "dvdsle.mm"
include "syl.mm"
include "cr.mm"
include "nnre.mm"
include "eluzelre.mm"
include "3anim123i.mm"
include "3anrot.mm"
include "sylibr.mm"
include "lelttr.mm"
include "expcomd.mm"
include "3exp.mm"
include "com34.mm"
include "3imp1.mm"
include "imp.mm"
include "nnz.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "zltlem1.mm"
include "mpbid.mm"
include "ex.mm"
include "syldc.mm"
include "impcom.mm"
include "peano2zm.mm"
include "anim1i.mm"
include "ancomd.mm"
include "elfz5.mm"
include "mpbird.mm"
include "weq.mm"
include "breq1.mm"
include "adantl.mm"
include "simprr.mm"
include "rspcedvd.mm"
include "rexnal.mm"
include "notnotb.mm"
include "bicomi.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "olcd.mm"
include "df-nel.mm"
include "ianor.mm"
include "isprm3.mm"
include "xchnxbir.mm"
include "bitri.mm"
include "rexlimdva.mm"
include "sylbid.mm"

theorem ncoprmlnprm
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j


  assert |- ( ( A e. NN /\ B e. NN /\ A < B ) -> ( 1 < ( A gcd B ) -> B e/ Prime ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    c1
    cA
    cB
    cgcd
    co
    clt
    wbr
    #
    vi
    cv
    #
    cA
    cdvds
    wbr
    #
    @5
    cB
    cdvds
    wbr
    #
    wa
    #
    vi
    c2
    cuz
    cfv
    #
    wrex
    #
    cB
    cprime
    wnel
    #
    @0
    @1
    @4
    @10
    wb
    @2
    @0
    @1
    wa
    @10
    @4
    cA
    cB
    vi
    ncoprmgcdgt1b
    bicomd
    3adant3
    @3
    @8
    @11
    vi
    @9
    @3
    @5
    @9
    wcel
    #
    wa
    #
    @8
    @11
    @13
    @8
    wa
    #
    cB
    @9
    wcel
    #
    wn
    #
    vj
    cv
    #
    cB
    cdvds
    wbr
    #
    wn
    #
    vj
    c2
    cB
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wn
    #
    wo
    #
    @11
    @14
    @23
    @16
    @14
    @18
    vj
    @21
    wrex
    #
    @23
    @14
    @18
    @7
    vj
    @5
    @21
    @14
    @5
    @21
    wcel
    #
    @5
    @20
    cle
    wbr
    #
    @8
    @13
    @27
    @6
    @13
    @27
    wi
    @7
    @13
    @6
    @5
    cA
    cle
    wbr
    #
    @27
    @13
    @5
    cz
    wcel
    #
    @0
    wa
    @6
    @28
    wi
    @3
    @0
    @12
    @29
    @0
    @1
    @2
    simp1
    c2
    @5
    eluzelz
    #
    anim12ci
    @5
    cA
    dvdsle
    syl
    @13
    @28
    @27
    @13
    @28
    wa
    #
    @5
    cB
    clt
    wbr
    #
    @27
    @13
    @28
    @32
    @0
    @1
    @2
    @12
    @28
    @32
    wi
    #
    @0
    @1
    @12
    @2
    @33
    @0
    @1
    @12
    @2
    @33
    wi
    @0
    @1
    @12
    w3a
    #
    @28
    @2
    @32
    @34
    @5
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    w3a
    #
    @28
    @2
    wa
    @32
    wi
    @34
    @36
    @37
    @35
    w3a
    @38
    @0
    @36
    @1
    @37
    @12
    @35
    cA
    nnre
    cB
    nnre
    c2
    @5
    eluzelre
    3anim123i
    @35
    @36
    @37
    3anrot
    sylibr
    @5
    cA
    cB
    lelttr
    syl
    expcomd
    3exp
    com34
    3imp1
    imp
    @31
    @29
    cB
    cz
    wcel
    #
    wa
    #
    @32
    @27
    wb
    @13
    @40
    @28
    @3
    @39
    @12
    @29
    @1
    @0
    @39
    @2
    cB
    nnz
    #
    3ad2ant2
    @30
    anim12ci
    adantr
    @5
    cB
    zltlem1
    syl
    mpbid
    ex
    syldc
    adantr
    impcom
    @14
    @12
    @20
    cz
    wcel
    #
    wa
    #
    @26
    @27
    wb
    @13
    @43
    @8
    @13
    @42
    @12
    @3
    @42
    @12
    @1
    @0
    @42
    @2
    @1
    @39
    @42
    @41
    cB
    peano2zm
    syl
    3ad2ant2
    anim1i
    ancomd
    adantr
    @5
    c2
    @20
    elfz5
    syl
    mpbird
    vj
    vi
    weq
    @18
    @7
    wb
    @14
    @17
    @5
    cB
    cdvds
    breq1
    adantl
    @13
    @6
    @7
    simprr
    rspcedvd
    @23
    @19
    wn
    #
    vj
    @21
    wrex
    @25
    @19
    vj
    @21
    rexnal
    @44
    @18
    vj
    @21
    @18
    @44
    @18
    notnotb
    bicomi
    rexbii
    bitr3i
    sylibr
    olcd
    @11
    cB
    cprime
    wcel
    #
    wn
    @24
    cB
    cprime
    df-nel
    @15
    @22
    wa
    @24
    @45
    @15
    @22
    ianor
    vj
    cB
    isprm3
    xchnxbir
    bitri
    sylibr
    ex
    rexlimdva
    sylbid
end
