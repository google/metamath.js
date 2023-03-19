include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "ctp.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfn.mm"
include "wn.mm"
include "simpl3.mm"
include "prfi.mm"
include "a1i.mm"
include "w3o.mm"
include "wo.mm"
include "wi.mm"
include "elprg.mm"
include "orcom.mm"
include "nne.mm"
include "eqcom.mm"
include "bitr2i.mm"
include "bicomi.mm"
include "orbi12i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "olcd.mm"
include "ex.mm"
include "3orass.mm"
include "syl6ibr.mm"
include "3ianor.mm"
include "con2d.mm"
include "hashunsng.mm"
include "syl12anc.mm"
include "simpr1.mm"
include "wb.mm"
include "3simpa.mm"
include "adantr.mm"
include "hashprg.mm"
include "syl.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "df-tp.mm"
include "fveq2i.mm"
include "df-3.mm"
include "3eqtr4g.mm"
include "cle.mm"
include "wbr.mm"
include "hashprlei.mm"
include "clt.mm"
include "cz.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "ax-mp.mm"
include "2z.mm"
include "zleltp1.mm"
include "2p1e3.mm"
include "breq2d.mm"
include "sylbid.mm"
include "mp2an.mm"
include "cr.mm"
include "nn0red.mm"
include "3re.mm"
include "ltnei.mm"
include "necomd.mm"
include "adantl.mm"
include "mp1i.mm"
include "tpeq1.mm"
include "tpidm12.mm"
include "syl6req.mm"
include "fveq2d.mm"
include "neeq1d.mm"
include "syl5ib.mm"
include "sylbi.mm"
include "tpeq2.mm"
include "tpidm23.mm"
include "tpeq3.mm"
include "tpidm13.mm"
include "3jaoi.mm"
include "com12.mm"
include "necon4bd.mm"
include "impbid.mm"

theorem hashtpg
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( A e. U /\ B e. V /\ C e. W ) -> ( ( A =/= B /\ B =/= C /\ C =/= A ) <-> ( # ` { A , B , C } ) = 3 ) )

  proof
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    cC
    cA
    wne
    #
    w3a
    #
    cA
    cB
    cC
    ctp
    #
    chash
    cfv
    #
    c3
    wceq
    #
    @3
    @7
    @10
    @3
    @7
    wa
    #
    cA
    cB
    cpr
    #
    cC
    csn
    cun
    #
    chash
    cfv
    #
    c2
    c1
    caddc
    co
    #
    @9
    c3
    @11
    @14
    @12
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @15
    @11
    @2
    @12
    cfn
    wcel
    #
    cC
    @12
    wcel
    #
    wn
    #
    @14
    @17
    wceq
    #
    @0
    @1
    @2
    @7
    simpl3
    @18
    @11
    cA
    cB
    prfi
    #
    a1i
    @3
    @7
    @20
    @3
    @19
    @7
    @3
    @19
    @4
    wn
    #
    @5
    wn
    #
    @6
    wn
    #
    w3o
    #
    @7
    wn
    #
    @3
    @19
    @23
    @24
    @25
    wo
    #
    wo
    #
    @26
    @3
    @19
    @29
    @3
    @19
    wa
    @28
    @23
    @3
    @19
    @28
    @2
    @0
    @19
    @28
    wi
    @1
    @2
    @19
    @28
    @2
    @19
    cC
    cA
    wceq
    #
    cC
    cB
    wceq
    #
    wo
    #
    @28
    cC
    cA
    cB
    cW
    elprg
    @32
    @31
    @30
    wo
    @28
    @30
    @31
    orcom
    @31
    @24
    @30
    @25
    @24
    cB
    cC
    wceq
    #
    @31
    cB
    cC
    nne
    #
    cB
    cC
    eqcom
    bitr2i
    @25
    @30
    cC
    cA
    nne
    #
    bicomi
    orbi12i
    bitri
    syl6bb
    biimpd
    3ad2ant3
    imp
    olcd
    ex
    @23
    @24
    @25
    3orass
    syl6ibr
    @4
    @5
    @6
    3ianor
    #
    syl6ibr
    con2d
    imp
    @2
    @18
    @20
    wa
    @21
    @12
    cC
    cW
    hashunsng
    imp
    syl12anc
    @11
    @16
    c2
    c1
    caddc
    @11
    @4
    @16
    c2
    wceq
    #
    @3
    @4
    @5
    @6
    simpr1
    @11
    @0
    @1
    wa
    #
    @4
    @37
    wb
    @3
    @38
    @7
    @0
    @1
    @2
    3simpa
    adantr
    cA
    cB
    cU
    cV
    hashprg
    syl
    mpbid
    oveq1d
    eqtrd
    @8
    @13
    chash
    cA
    cB
    cC
    df-tp
    fveq2i
    df-3
    3eqtr4g
    ex
    @3
    @7
    @9
    c3
    @27
    @3
    @9
    c3
    wne
    #
    @27
    @26
    @3
    @39
    wi
    #
    @36
    @23
    @40
    @24
    @25
    @23
    cA
    cB
    wceq
    #
    @40
    cA
    cB
    nne
    @3
    cB
    cC
    cpr
    #
    chash
    cfv
    #
    c3
    wne
    #
    @41
    @39
    @42
    cfn
    wcel
    #
    @43
    c2
    cle
    wbr
    #
    wa
    @44
    @3
    cB
    cC
    hashprlei
    @46
    @44
    @45
    @46
    c3
    @43
    @46
    @43
    c3
    clt
    wbr
    #
    c3
    @43
    wne
    @43
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    @46
    @47
    wi
    @45
    @48
    cB
    cC
    prfi
    #
    @45
    @43
    @42
    hashcl
    #
    nn0zd
    ax-mp
    2z
    @48
    @49
    wa
    #
    @46
    @43
    @15
    clt
    wbr
    #
    @47
    @43
    c2
    zleltp1
    @52
    @53
    @47
    @52
    @15
    c3
    @43
    clt
    @15
    c3
    wceq
    #
    @52
    2p1e3
    a1i
    breq2d
    biimpd
    sylbid
    mp2an
    @43
    c3
    @45
    @43
    cr
    wcel
    @50
    @45
    @43
    @51
    nn0red
    ax-mp
    3re
    ltnei
    syl
    necomd
    adantl
    mp1i
    @41
    @43
    @9
    c3
    @41
    @42
    @8
    chash
    @41
    @8
    cB
    cB
    cC
    ctp
    @42
    cA
    cB
    cB
    cC
    tpeq1
    cB
    cC
    tpidm12
    syl6req
    fveq2d
    neeq1d
    syl5ib
    sylbi
    @24
    @33
    @40
    @34
    @3
    cA
    cC
    cpr
    #
    chash
    cfv
    #
    c3
    wne
    #
    @33
    @39
    @55
    cfn
    wcel
    #
    @56
    c2
    cle
    wbr
    #
    wa
    @57
    @3
    cA
    cC
    hashprlei
    @59
    @57
    @58
    @59
    c3
    @56
    @59
    @56
    c3
    clt
    wbr
    #
    c3
    @56
    wne
    @56
    cz
    wcel
    #
    @49
    @59
    @60
    wi
    @58
    @61
    cA
    cC
    prfi
    #
    @58
    @56
    @55
    hashcl
    #
    nn0zd
    ax-mp
    2z
    @61
    @49
    wa
    #
    @59
    @56
    @15
    clt
    wbr
    #
    @60
    @56
    c2
    zleltp1
    @64
    @65
    @60
    @64
    @15
    c3
    @56
    clt
    @54
    @64
    2p1e3
    a1i
    breq2d
    biimpd
    sylbid
    mp2an
    @56
    c3
    @58
    @56
    cr
    wcel
    @62
    @58
    @56
    @63
    nn0red
    ax-mp
    3re
    ltnei
    syl
    necomd
    adantl
    mp1i
    @33
    @56
    @9
    c3
    @33
    @55
    @8
    chash
    @33
    @8
    cA
    cC
    cC
    ctp
    @55
    cB
    cC
    cA
    cC
    tpeq2
    cA
    cC
    tpidm23
    syl6req
    fveq2d
    neeq1d
    syl5ib
    sylbi
    @25
    @30
    @40
    @35
    @3
    @16
    c3
    wne
    #
    @30
    @39
    @18
    @16
    c2
    cle
    wbr
    #
    wa
    @66
    @3
    cA
    cB
    hashprlei
    @67
    @66
    @18
    @67
    c3
    @16
    @67
    @16
    c3
    clt
    wbr
    #
    c3
    @16
    wne
    @16
    cz
    wcel
    #
    @49
    @67
    @68
    wi
    @18
    @69
    @22
    @18
    @16
    @12
    hashcl
    #
    nn0zd
    ax-mp
    2z
    @69
    @49
    wa
    #
    @67
    @16
    @15
    clt
    wbr
    #
    @68
    @16
    c2
    zleltp1
    @71
    @72
    @68
    @71
    @15
    c3
    @16
    clt
    @54
    @71
    2p1e3
    a1i
    breq2d
    biimpd
    sylbid
    mp2an
    @16
    c3
    @18
    @16
    cr
    wcel
    @22
    @18
    @16
    @70
    nn0red
    ax-mp
    3re
    ltnei
    syl
    necomd
    adantl
    mp1i
    @30
    @16
    @9
    c3
    @30
    @12
    @8
    chash
    @30
    @8
    cA
    cB
    cA
    ctp
    @12
    cC
    cA
    cA
    cB
    tpeq3
    cA
    cB
    tpidm13
    syl6req
    fveq2d
    neeq1d
    syl5ib
    sylbi
    3jaoi
    sylbi
    com12
    necon4bd
    impbid
end
