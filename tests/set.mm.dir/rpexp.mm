include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cgcd.mm"
include "c1.mm"
include "wb.mm"
include "wi.mm"
include "0exp.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "oveq12.mm"
include "sylan.mm"
include "bibi12d.mm"
include "syl5ibrcom.mm"
include "3ad2ant3.mm"
include "wn.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "exprmfct.mm"
include "cn0.mm"
include "simpl1.mm"
include "simpl3.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpl2.mm"
include "gcddvds.mm"
include "simpld.mm"
include "prmz.mm"
include "adantl.mm"
include "simpr.mm"
include "cc.mm"
include "zcnd.mm"
include "expeq0.mm"
include "anbi1d.mm"
include "mtbird.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnzd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "simpll1.mm"
include "prmdvdsexp.mm"
include "sylibd.mm"
include "simprd.mm"
include "jcad.mm"
include "dvdsgcd.mm"
include "nprmdvds1.mm"
include "breq2.mm"
include "notbid.mm"
include "necon2ad.mm"
include "3syld.mm"
include "rexlimdva.mm"
include "3adantl3.mm"
include "eluz2b3.mm"
include "baib.mm"
include "syl.mm"
include "sylibrd.mm"
include "syl5.mm"
include "iddvdsexp.mm"
include "mp2and.mm"
include "impbid.mm"
include "3bitr3d.mm"
include "necon4bid.mm"
include "ex.mm"
include "pm2.61d.mm"

theorem rpexp
  let cA: class A
  let cB: class B
  let cN: class N
  let vp: setvar p


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ N e. NN ) -> ( ( ( A ^ N ) gcd B ) = 1 <-> ( A gcd B ) = 1 ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    #
    cA
    cN
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wb
    #
    @2
    @0
    @6
    @12
    wi
    @1
    @2
    @12
    @6
    cc0
    cN
    cexp
    co
    #
    cc0
    cgcd
    co
    #
    c1
    wceq
    #
    cc0
    cc0
    cgcd
    co
    #
    c1
    wceq
    #
    wb
    @2
    @14
    @16
    c1
    @2
    @13
    cc0
    cc0
    cgcd
    cN
    0exp
    oveq1d
    eqeq1d
    @6
    @9
    @15
    @11
    @17
    @6
    @8
    @14
    c1
    @4
    @7
    @13
    wceq
    @5
    @8
    @14
    wceq
    cA
    cc0
    cN
    cexp
    oveq1
    @7
    @13
    cB
    cc0
    cgcd
    oveq12
    sylan
    eqeq1d
    @6
    @10
    @16
    c1
    cA
    cc0
    cB
    cc0
    cgcd
    oveq12
    eqeq1d
    bibi12d
    syl5ibrcom
    3ad2ant3
    @3
    @6
    wn
    #
    @12
    @3
    @18
    wa
    #
    @8
    c1
    @10
    c1
    @19
    @8
    c2
    cuz
    cfv
    #
    wcel
    #
    @10
    @20
    wcel
    #
    @8
    c1
    wne
    #
    @10
    c1
    wne
    #
    @19
    @21
    @22
    @21
    vp
    cv
    #
    @8
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @19
    @22
    @8
    vp
    exprmfct
    @19
    @27
    @24
    @22
    @19
    @26
    @24
    vp
    cprime
    @19
    @25
    cprime
    wcel
    #
    wa
    #
    @26
    @25
    cA
    cdvds
    wbr
    #
    @25
    cB
    cdvds
    wbr
    #
    wa
    #
    @25
    @10
    cdvds
    wbr
    #
    @24
    @29
    @26
    @30
    @31
    @29
    @26
    @25
    @7
    cdvds
    wbr
    #
    @30
    @29
    @26
    @8
    @7
    cdvds
    wbr
    #
    @34
    @29
    @35
    @8
    cB
    cdvds
    wbr
    #
    @29
    @7
    cz
    wcel
    #
    @1
    @35
    @36
    wa
    @19
    @37
    @28
    @19
    @0
    cN
    cn0
    wcel
    @37
    @0
    @1
    @2
    @18
    simpl1
    #
    @19
    cN
    @0
    @1
    @2
    @18
    simpl3
    #
    nnnn0d
    cA
    cN
    zexpcl
    syl2anc
    #
    adantr
    #
    @19
    @1
    @28
    @0
    @1
    @2
    @18
    simpl2
    #
    adantr
    #
    @7
    cB
    gcddvds
    syl2anc
    #
    simpld
    @29
    @25
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @37
    @26
    @35
    wa
    @34
    wi
    @28
    @45
    @19
    @25
    prmz
    adantl
    #
    @19
    @46
    @28
    @19
    @8
    @19
    @37
    @1
    @7
    cc0
    wceq
    #
    @5
    wa
    #
    wn
    @8
    cn
    wcel
    #
    @40
    @42
    @19
    @49
    @6
    @3
    @18
    simpr
    @19
    @48
    @4
    @5
    @19
    cA
    cc
    wcel
    @2
    @48
    @4
    wb
    @19
    cA
    @38
    zcnd
    @39
    cA
    cN
    expeq0
    syl2anc
    anbi1d
    mtbird
    @7
    cB
    gcdn0cl
    syl21anc
    #
    nnzd
    adantr
    #
    @41
    @25
    @8
    @7
    dvdstr
    syl3anc
    mpan2d
    @29
    @28
    @0
    @2
    @34
    @30
    wb
    @19
    @28
    simpr
    @0
    @1
    @2
    @18
    @28
    simpll1
    #
    @19
    @2
    @28
    @39
    adantr
    #
    cA
    @25
    cN
    prmdvdsexp
    syl3anc
    sylibd
    @29
    @26
    @36
    @31
    @29
    @35
    @36
    @44
    simprd
    @29
    @45
    @46
    @1
    @26
    @36
    wa
    @31
    wi
    @47
    @52
    @43
    @25
    @8
    cB
    dvdstr
    syl3anc
    mpan2d
    jcad
    @29
    @45
    @0
    @1
    @32
    @33
    wi
    @47
    @53
    @43
    @25
    cA
    cB
    dvdsgcd
    syl3anc
    @28
    @33
    @24
    wi
    @19
    @28
    @33
    @10
    c1
    @28
    @33
    wn
    @11
    @25
    c1
    cdvds
    wbr
    #
    wn
    #
    @25
    nprmdvds1
    #
    @11
    @33
    @55
    @10
    c1
    @25
    cdvds
    breq2
    notbid
    syl5ibrcom
    necon2ad
    adantl
    3syld
    rexlimdva
    @19
    @10
    cn
    wcel
    #
    @22
    @24
    wb
    @0
    @1
    @18
    @58
    @2
    cA
    cB
    gcdn0cl
    3adantl3
    #
    @22
    @58
    @24
    @10
    eluz2b3
    baib
    syl
    #
    sylibrd
    syl5
    @22
    @33
    vp
    cprime
    wrex
    #
    @19
    @21
    @10
    vp
    exprmfct
    @19
    @61
    @23
    @21
    @19
    @33
    @23
    vp
    cprime
    @29
    @33
    @34
    @31
    wa
    #
    @26
    @23
    @29
    @33
    @34
    @31
    @29
    @33
    @10
    @7
    cdvds
    wbr
    #
    @34
    @29
    @10
    cA
    cdvds
    wbr
    #
    cA
    @7
    cdvds
    wbr
    #
    @63
    @29
    @64
    @10
    cB
    cdvds
    wbr
    #
    @29
    @0
    @1
    @64
    @66
    wa
    @53
    @43
    cA
    cB
    gcddvds
    syl2anc
    #
    simpld
    @29
    @0
    @2
    @65
    @53
    @54
    cA
    cN
    iddvdsexp
    syl2anc
    @29
    @10
    cz
    wcel
    #
    @0
    @37
    @64
    @65
    wa
    @63
    wi
    @19
    @68
    @28
    @19
    @10
    @59
    nnzd
    adantr
    #
    @53
    @41
    @10
    cA
    @7
    dvdstr
    syl3anc
    mp2and
    @29
    @45
    @68
    @37
    @33
    @63
    wa
    @34
    wi
    @47
    @69
    @41
    @25
    @10
    @7
    dvdstr
    syl3anc
    mpan2d
    @29
    @33
    @66
    @31
    @29
    @64
    @66
    @67
    simprd
    @29
    @45
    @68
    @1
    @33
    @66
    wa
    @31
    wi
    @47
    @69
    @43
    @25
    @10
    cB
    dvdstr
    syl3anc
    mpan2d
    jcad
    @29
    @45
    @37
    @1
    @62
    @26
    wi
    @47
    @41
    @43
    @25
    @7
    cB
    dvdsgcd
    syl3anc
    @28
    @26
    @23
    wi
    @19
    @28
    @26
    @8
    c1
    @28
    @26
    wn
    @9
    @56
    @57
    @9
    @26
    @55
    @8
    c1
    @25
    cdvds
    breq2
    notbid
    syl5ibrcom
    necon2ad
    adantl
    3syld
    rexlimdva
    @19
    @50
    @21
    @23
    wb
    @51
    @21
    @50
    @23
    @8
    eluz2b3
    baib
    syl
    #
    sylibrd
    syl5
    impbid
    @70
    @60
    3bitr3d
    necon4bid
    ex
    pm2.61d
end
