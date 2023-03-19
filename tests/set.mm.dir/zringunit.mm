include "zring.mm"
include "cui.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cabs.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "zringbas.mm"
include "eqid.mm"
include "unitcl.mm"
include "ccnfld.mm"
include "cgz.mm"
include "cress.mm"
include "co.mm"
include "csubrg.mm"
include "wss.mm"
include "zsubrg.mm"
include "cv.mm"
include "zgz.mm"
include "ssriv.mm"
include "wb.mm"
include "gzsubrg.mm"
include "subsubrg.mm"
include "ax-mp.mm"
include "mpbir2an.mm"
include "df-zring.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "subrguss.mm"
include "sseli.mm"
include "gzrngunit.mm"
include "simprbi.mm"
include "syl.mm"
include "jca.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cinvr.mm"
include "wne.mm"
include "zcn.mm"
include "adantr.mm"
include "simpr.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simpl.mm"
include "cdiv.mm"
include "cnfldinv.mm"
include "syl2anc.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "cr.mm"
include "zre.mm"
include "absresq.mm"
include "oveq1d.mm"
include "sq1.mm"
include "sqvald.mm"
include "3eqtr3rd.mm"
include "1cnd.mm"
include "divmuld.mm"
include "mpbird.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "subrgunit.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem zringunit
  let cA: class A
  let vx: setvar x


  assert |- ( A e. ( Unit ` ZZring ) <-> ( A e. ZZ /\ ( abs ` A ) = 1 ) )

  proof
    cA
    zring
    cui
    cfv
    #
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @1
    @2
    @4
    cz
    zring
    @0
    cA
    zringbas
    @0
    eqid
    #
    unitcl
    @1
    cA
    ccnfld
    cgz
    cress
    co
    #
    cui
    cfv
    #
    wcel
    #
    @4
    @0
    @8
    cA
    cz
    @7
    csubrg
    cfv
    wcel
    #
    @0
    @8
    wss
    @10
    cz
    ccnfld
    csubrg
    cfv
    #
    wcel
    #
    cz
    cgz
    wss
    #
    zsubrg
    vx
    cz
    cgz
    vx
    cv
    zgz
    ssriv
    #
    cgz
    @11
    wcel
    #
    @10
    @12
    @13
    wa
    wb
    gzsubrg
    cgz
    cz
    ccnfld
    @7
    @7
    eqid
    #
    subsubrg
    ax-mp
    mpbir2an
    cz
    @7
    zring
    @8
    @0
    zring
    ccnfld
    cz
    cress
    co
    #
    @7
    cz
    cress
    co
    #
    df-zring
    @15
    @13
    @18
    @17
    wceq
    gzsubrg
    @14
    cgz
    cz
    ccnfld
    @11
    ressabs
    mp2an
    eqtr4i
    @8
    eqid
    @6
    subrguss
    ax-mp
    sseli
    @9
    cA
    cgz
    wcel
    @4
    cA
    @7
    @16
    gzrngunit
    simprbi
    syl
    jca
    @5
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @2
    cA
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    cz
    wcel
    #
    @1
    @5
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    @20
    @2
    @24
    @4
    cA
    zcn
    adantr
    #
    @5
    @3
    cc0
    wne
    @25
    @5
    @3
    c1
    cc0
    @2
    @4
    simpr
    #
    c1
    cc0
    wne
    @5
    ax-1ne0
    a1i
    eqnetrd
    cA
    cc0
    @3
    cc0
    cA
    cc0
    wceq
    @3
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    necon3i
    syl
    #
    cA
    cc
    cc0
    eldifsn
    sylanbrc
    @2
    @4
    simpl
    #
    @5
    @22
    cA
    cz
    @5
    @22
    c1
    cA
    cdiv
    co
    #
    cA
    @5
    @24
    @25
    @22
    @30
    wceq
    @26
    @28
    cA
    cnfldinv
    syl2anc
    @5
    @30
    cA
    wceq
    cA
    cA
    cmul
    co
    #
    c1
    wceq
    @5
    @3
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    c1
    @31
    @5
    cA
    cr
    wcel
    #
    @32
    @33
    wceq
    @2
    @34
    @4
    cA
    zre
    adantr
    cA
    absresq
    syl
    @5
    @32
    c1
    c2
    cexp
    co
    c1
    @5
    @3
    c1
    c2
    cexp
    @27
    oveq1d
    sq1
    syl6eq
    @5
    cA
    @26
    sqvald
    3eqtr3rd
    @5
    c1
    cA
    cA
    @5
    1cnd
    @26
    @26
    @28
    divmuld
    mpbird
    eqtrd
    @29
    eqeltrd
    @12
    @1
    @20
    @2
    @23
    w3a
    wb
    zsubrg
    cz
    ccnfld
    zring
    @19
    @21
    @0
    cA
    df-zring
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @6
    @21
    eqid
    subrgunit
    ax-mp
    syl3anbrc
    impbii
end
