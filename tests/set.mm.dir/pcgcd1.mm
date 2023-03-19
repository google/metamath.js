include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cgcd.mm"
include "wceq.mm"
include "cc0.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "wne.mm"
include "cdvds.mm"
include "simpl1.mm"
include "wn.mm"
include "cn.mm"
include "simp2.mm"
include "adantr.mm"
include "simpl3.mm"
include "simprr.mm"
include "simpr.mm"
include "necon3ai.mm"
include "syl.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnzd.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "pcdvdstr.mm"
include "syl13anc.mm"
include "cexp.mm"
include "cr.mm"
include "cxr.mm"
include "cmnf.mm"
include "clt.mm"
include "cq.mm"
include "zq.mm"
include "pcxcl.mm"
include "cn0.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "nn0red.mm"
include "pcge0.mm"
include "ge0gtmnf.mm"
include "simprl.mm"
include "xrre.mm"
include "syl22anc.mm"
include "cpnf.mm"
include "pnfnre.mm"
include "neli.mm"
include "pc0.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "mpd.mm"
include "pczdvds.mm"
include "wb.mm"
include "pcdvdsb.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wi.mm"
include "prmnn.mm"
include "nnexpcld.mm"
include "dvdsgcd.mm"
include "mp2and.mm"
include "mpbird.mm"
include "pccld.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "anassrs.mm"
include "cabs.mm"
include "cfv.mm"
include "gcdid0.mm"
include "pcabs.mm"
include "sylan2.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "pm2.61ne.mm"

theorem pcgcd1
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( ( P e. Prime /\ A e. ZZ /\ B e. ZZ ) /\ ( P pCnt A ) <_ ( P pCnt B ) ) -> ( P pCnt ( A gcd B ) ) = ( P pCnt A ) )

  proof
    cP
    cprime
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
    w3a
    #
    cP
    cA
    cpc
    co
    #
    cP
    cB
    cpc
    co
    #
    cle
    wbr
    #
    wa
    cP
    cA
    cB
    cgcd
    co
    #
    cpc
    co
    #
    @4
    wceq
    #
    cP
    cA
    cc0
    cgcd
    co
    #
    cpc
    co
    #
    @4
    wceq
    #
    cB
    cc0
    cB
    cc0
    wceq
    #
    @8
    @11
    @4
    @13
    @7
    @10
    cP
    cpc
    cB
    cc0
    cA
    cgcd
    oveq2
    oveq2d
    eqeq1d
    @3
    @6
    cB
    cc0
    wne
    #
    @9
    @3
    @6
    @14
    wa
    #
    wa
    #
    @9
    @8
    @4
    cle
    wbr
    #
    @4
    @8
    cle
    wbr
    #
    @16
    @0
    @7
    cz
    wcel
    #
    @1
    @7
    cA
    cdvds
    wbr
    #
    @17
    @0
    @1
    @2
    @15
    simpl1
    #
    @16
    @7
    @16
    @1
    @2
    cA
    cc0
    wceq
    #
    @13
    wa
    #
    wn
    #
    @7
    cn
    wcel
    @3
    @1
    @15
    @0
    @1
    @2
    simp2
    #
    adantr
    #
    @0
    @1
    @2
    @15
    simpl3
    #
    @16
    @14
    @24
    @3
    @6
    @14
    simprr
    #
    @23
    cB
    cc0
    @22
    @13
    simpr
    necon3ai
    syl
    cA
    cB
    gcdn0cl
    syl21anc
    #
    nnzd
    #
    @26
    @16
    @20
    @7
    cB
    cdvds
    wbr
    #
    @16
    @1
    @2
    @20
    @31
    wa
    @26
    @27
    cA
    cB
    gcddvds
    syl2anc
    simpld
    @7
    cA
    cP
    pcdvdstr
    syl13anc
    @16
    @18
    cP
    @4
    cexp
    co
    #
    @7
    cdvds
    wbr
    #
    @16
    @32
    cA
    cdvds
    wbr
    #
    @32
    cB
    cdvds
    wbr
    #
    @33
    @16
    @0
    @1
    cA
    cc0
    wne
    #
    @34
    @21
    @26
    @16
    @4
    cr
    wcel
    #
    @36
    @16
    @4
    cxr
    wcel
    #
    @5
    cr
    wcel
    cmnf
    @4
    clt
    wbr
    #
    @6
    @37
    @16
    @0
    cA
    cq
    wcel
    #
    @38
    @21
    @16
    @1
    @40
    @26
    cA
    zq
    #
    syl
    cP
    cA
    pcxcl
    syl2anc
    #
    @16
    @5
    @16
    @0
    @2
    @14
    @5
    cn0
    wcel
    @21
    @27
    @28
    cP
    cB
    pczcl
    syl12anc
    nn0red
    @16
    @38
    cc0
    @4
    cle
    wbr
    #
    @39
    @42
    @16
    @0
    @1
    @43
    @21
    @26
    cP
    cA
    pcge0
    syl2anc
    @4
    ge0gtmnf
    syl2anc
    @3
    @6
    @14
    simprl
    #
    @4
    @5
    xrre
    syl22anc
    #
    @16
    @37
    cA
    cc0
    @16
    @37
    wn
    @22
    cP
    cc0
    cpc
    co
    #
    cr
    wcel
    #
    wn
    @16
    @47
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    @16
    @46
    cpnf
    cr
    @16
    @0
    @46
    cpnf
    wceq
    @21
    cP
    pc0
    syl
    eleq1d
    mtbiri
    @22
    @37
    @47
    @22
    @4
    @46
    cr
    cA
    cc0
    cP
    cpc
    oveq2
    eleq1d
    notbid
    syl5ibrcom
    necon2ad
    mpd
    #
    cP
    cA
    pczdvds
    syl12anc
    @16
    @6
    @35
    @44
    @16
    @0
    @2
    @4
    cn0
    wcel
    #
    @6
    @35
    wb
    @21
    @27
    @16
    @0
    @1
    @36
    @49
    @21
    @26
    @48
    cP
    cA
    pczcl
    syl12anc
    #
    @4
    cP
    cB
    pcdvdsb
    syl3anc
    mpbid
    @16
    @32
    cz
    wcel
    @1
    @2
    @34
    @35
    wa
    @33
    wi
    @16
    @32
    @16
    cP
    @4
    @16
    @0
    cP
    cn
    wcel
    @21
    cP
    prmnn
    syl
    @50
    nnexpcld
    nnzd
    @26
    @27
    @32
    cA
    cB
    dvdsgcd
    syl3anc
    mp2and
    @16
    @0
    @19
    @49
    @18
    @33
    wb
    @21
    @30
    @50
    @4
    cP
    @7
    pcdvdsb
    syl3anc
    mpbird
    @16
    @8
    @4
    @16
    @8
    @16
    cP
    @7
    @21
    @29
    pccld
    nn0red
    @45
    letri3d
    mpbir2and
    anassrs
    @3
    @12
    @6
    @3
    @11
    cP
    cA
    cabs
    cfv
    #
    cpc
    co
    #
    @4
    @3
    @10
    @51
    cP
    cpc
    @3
    @1
    @10
    @51
    wceq
    @25
    cA
    gcdid0
    syl
    oveq2d
    @0
    @1
    @52
    @4
    wceq
    #
    @2
    @1
    @0
    @40
    @53
    @41
    cA
    cP
    pcabs
    sylan2
    3adant3
    eqtrd
    adantr
    pm2.61ne
end
