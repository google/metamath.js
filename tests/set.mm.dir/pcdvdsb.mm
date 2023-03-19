include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cn0.mm"
include "w3a.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "cdvds.mm"
include "wb.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "breq2.mm"
include "bibi12d.mm"
include "wne.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "simpl3.mm"
include "nn0zd.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "eluz.mm"
include "syl2anc.mm"
include "wi.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "nnzd.mm"
include "dvdsexp.mm"
include "3expia.mm"
include "sylbird.mm"
include "pczdvds.mm"
include "nnexpcl.mm"
include "sylan.mm"
include "3adant2.mm"
include "adantr.mm"
include "nnexpcld.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syld.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "cr.mm"
include "nn0re.mm"
include "ltnle.mm"
include "syl2an.mm"
include "nn0ltp1le.mm"
include "bitr3d.mm"
include "peano2nn0.mm"
include "pczndvds.mm"
include "mtod.mm"
include "imnan.mm"
include "sylibr.mm"
include "sylbid.mm"
include "impcon4bid.mm"
include "cpnf.mm"
include "cxr.mm"
include "3ad2ant3.mm"
include "rexrd.mm"
include "pnfge.mm"
include "pc0.mm"
include "3ad2ant1.mm"
include "breqtrrd.mm"
include "dvds0.mm"
include "2thd.mm"
include "pm2.61ne.mm"

theorem pcdvdsb
  let cA: class A
  let cP: class P
  let cN: class N


  assert |- ( ( P e. Prime /\ N e. ZZ /\ A e. NN0 ) -> ( A <_ ( P pCnt N ) <-> ( P ^ A ) || N ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cz
    wcel
    #
    cA
    cn0
    wcel
    #
    w3a
    #
    cA
    cP
    cN
    cpc
    co
    #
    cle
    wbr
    #
    cP
    cA
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    wb
    cA
    cP
    cc0
    cpc
    co
    #
    cle
    wbr
    #
    @6
    cc0
    cdvds
    wbr
    #
    wb
    cN
    cc0
    cN
    cc0
    wceq
    #
    @5
    @9
    @7
    @10
    @11
    @4
    @8
    cA
    cle
    cN
    cc0
    cP
    cpc
    oveq2
    breq2d
    cN
    cc0
    @6
    cdvds
    breq2
    bibi12d
    @3
    cN
    cc0
    wne
    #
    wa
    #
    @5
    @7
    @13
    @5
    @6
    cP
    @4
    cexp
    co
    #
    cdvds
    wbr
    #
    @7
    @13
    @5
    @4
    cA
    cuz
    cfv
    wcel
    #
    @15
    @13
    cA
    cz
    wcel
    #
    @4
    cz
    wcel
    @16
    @5
    wb
    @13
    cA
    @0
    @1
    @2
    @12
    simpl3
    #
    nn0zd
    #
    @13
    @4
    @13
    @0
    @1
    @12
    @4
    cn0
    wcel
    #
    @0
    @1
    @2
    @12
    simpl1
    #
    @0
    @1
    @2
    @12
    simpl2
    #
    @3
    @12
    simpr
    #
    cP
    cN
    pczcl
    syl12anc
    #
    nn0zd
    cA
    @4
    eluz
    syl2anc
    @13
    cP
    cz
    wcel
    #
    @2
    @16
    @15
    wi
    @13
    cP
    @13
    @0
    cP
    cn
    wcel
    #
    @21
    cP
    prmnn
    #
    syl
    #
    nnzd
    #
    @18
    @25
    @2
    @16
    @15
    cP
    cA
    @4
    dvdsexp
    3expia
    syl2anc
    sylbird
    @13
    @15
    @14
    cN
    cdvds
    wbr
    #
    @7
    @13
    @0
    @1
    @12
    @30
    @21
    @22
    @23
    cP
    cN
    pczdvds
    syl12anc
    @13
    @6
    cz
    wcel
    #
    @14
    cz
    wcel
    @1
    @15
    @30
    wa
    @7
    wi
    @3
    @31
    @12
    @3
    @6
    @0
    @2
    @6
    cn
    wcel
    #
    @1
    @0
    @26
    @2
    @32
    @27
    cP
    cA
    nnexpcl
    sylan
    3adant2
    nnzd
    #
    adantr
    #
    @13
    @14
    @13
    cP
    @4
    @28
    @24
    nnexpcld
    nnzd
    @22
    @6
    @14
    cN
    dvdstr
    syl3anc
    mpan2d
    syld
    @13
    @5
    wn
    #
    @4
    c1
    caddc
    co
    #
    cA
    cle
    wbr
    #
    @7
    wn
    #
    @13
    @20
    @2
    @35
    @37
    wb
    @24
    @18
    @20
    @2
    wa
    @4
    cA
    clt
    wbr
    #
    @35
    @37
    @20
    @4
    cr
    wcel
    cA
    cr
    wcel
    #
    @39
    @35
    wb
    @2
    @4
    nn0re
    cA
    nn0re
    #
    @4
    cA
    ltnle
    syl2an
    @4
    cA
    nn0ltp1le
    bitr3d
    syl2anc
    @13
    @37
    cP
    @36
    cexp
    co
    #
    @6
    cdvds
    wbr
    #
    @38
    @13
    @37
    cA
    @36
    cuz
    cfv
    wcel
    #
    @43
    @13
    @36
    cz
    wcel
    @17
    @44
    @37
    wb
    @13
    @36
    @13
    @20
    @36
    cn0
    wcel
    #
    @24
    @4
    peano2nn0
    syl
    #
    nn0zd
    @19
    @36
    cA
    eluz
    syl2anc
    @13
    @25
    @45
    @44
    @43
    wi
    @29
    @46
    @25
    @45
    @44
    @43
    cP
    @36
    cA
    dvdsexp
    3expia
    syl2anc
    sylbird
    @13
    @43
    @7
    wa
    #
    wn
    @43
    @38
    wi
    @13
    @47
    @42
    cN
    cdvds
    wbr
    #
    @13
    @0
    @1
    @12
    @48
    wn
    @21
    @22
    @23
    cP
    cN
    pczndvds
    syl12anc
    @13
    @42
    cz
    wcel
    @31
    @1
    @47
    @48
    wi
    @13
    @42
    @13
    cP
    @36
    @28
    @46
    nnexpcld
    nnzd
    @34
    @22
    @42
    @6
    cN
    dvdstr
    syl3anc
    mtod
    @43
    @7
    imnan
    sylibr
    syld
    sylbid
    impcon4bid
    @3
    @9
    @10
    @3
    cA
    cpnf
    @8
    cle
    @3
    cA
    cxr
    wcel
    cA
    cpnf
    cle
    wbr
    @3
    cA
    @2
    @0
    @40
    @1
    @41
    3ad2ant3
    rexrd
    cA
    pnfge
    syl
    @0
    @1
    @8
    cpnf
    wceq
    @2
    cP
    pc0
    3ad2ant1
    breqtrrd
    @3
    @31
    @10
    @33
    @6
    dvds0
    syl
    2thd
    pm2.61ne
end
