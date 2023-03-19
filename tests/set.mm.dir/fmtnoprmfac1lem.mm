include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "codz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "wa.mm"
include "cmo.mm"
include "cc0.mm"
include "eldifi.mm"
include "prmnn.mm"
include "syl.mm"
include "ad2antlr.mm"
include "wb.mm"
include "cn0.mm"
include "nnnn0.mm"
include "fmtno.mm"
include "breq2d.mm"
include "adantr.mm"
include "biimpa.mm"
include "dvdsmod0.mm"
include "syl2anc.mm"
include "ex.mm"
include "cneg.mm"
include "wi.mm"
include "cz.mm"
include "2nn.mm"
include "a1i.mm"
include "2nn0.mm"
include "nn0expcld.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "1zzd.mm"
include "adantl.mm"
include "summodnegmod.mm"
include "syl3anc.mm"
include "crp.mm"
include "neg1z.mm"
include "jctir.mm"
include "nnrpd.mm"
include "anim12i.mm"
include "simpr.mm"
include "modexp.mm"
include "cmul.mm"
include "cc.mm"
include "w3a.mm"
include "2cnd.mm"
include "3jca.mm"
include "expmul.mm"
include "expp1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "neg1sqe1.mm"
include "cr.mm"
include "clt.mm"
include "nnred.mm"
include "prmgt1.mm"
include "1mod.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "wne.mm"
include "simpll.mm"
include "sylan2.mm"
include "cmin.mm"
include "m1modnnsub1.mm"
include "eldifsni.mm"
include "necomd.mm"
include "nncnd.mm"
include "1cnd.mm"
include "subadd2d.mm"
include "1p1e2.mm"
include "eqeq1i.mm"
include "syl6bb.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "eqeq1.mm"
include "sylbid.mm"
include "imp.mm"
include "simplr.mm"
include "odz2prm2pw.mm"
include "syl12anc.mm"
include "syld.mm"
include "pm2.43d.mm"
include "3impia.mm"

theorem fmtnoprmfac1lem
  let cP: class P
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN /\ P e. ( Prime \ { 2 } ) /\ P || ( FermatNo ` N ) ) -> ( ( odZ ` P ) ` 2 ) = ( 2 ^ ( N + 1 ) ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cP
    cN
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    c2
    cP
    codz
    cfv
    cfv
    c2
    cN
    c1
    caddc
    co
    cexp
    co
    #
    wceq
    #
    @0
    @2
    wa
    #
    @4
    c2
    c2
    cN
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cP
    cmo
    co
    cc0
    wceq
    #
    @6
    @7
    @4
    @11
    @7
    @4
    wa
    cP
    cn
    wcel
    #
    cP
    @10
    cdvds
    wbr
    #
    @11
    @2
    @12
    @0
    @4
    @2
    cP
    cprime
    wcel
    #
    @12
    cP
    cprime
    @1
    eldifi
    #
    cP
    prmnn
    #
    syl
    #
    ad2antlr
    @7
    @4
    @13
    @0
    @4
    @13
    wb
    @2
    @0
    @3
    @10
    cP
    cdvds
    @0
    cN
    cn0
    wcel
    #
    @3
    @10
    wceq
    cN
    nnnn0
    #
    cN
    fmtno
    syl
    breq2d
    adantr
    biimpa
    cP
    @10
    dvdsmod0
    syl2anc
    ex
    @7
    @11
    @6
    @7
    @11
    @9
    cP
    cmo
    co
    #
    c1
    cneg
    #
    cP
    cmo
    co
    #
    wceq
    #
    @11
    @6
    wi
    #
    @7
    @9
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @12
    @11
    @23
    wb
    #
    @0
    @25
    @2
    @0
    @9
    @0
    c2
    @8
    c2
    cn
    wcel
    @0
    2nn
    a1i
    @0
    c2
    cN
    c2
    cn0
    wcel
    #
    @0
    2nn0
    a1i
    #
    @19
    nn0expcld
    #
    nnexpcld
    nnzd
    #
    adantr
    #
    @7
    1zzd
    @2
    @12
    @0
    @17
    adantl
    #
    @9
    c1
    cP
    summodnegmod
    #
    syl3anc
    @7
    @23
    @9
    c2
    cexp
    co
    #
    cP
    cmo
    co
    #
    @21
    c2
    cexp
    co
    #
    cP
    cmo
    co
    #
    wceq
    #
    @24
    @7
    @23
    @39
    @7
    @23
    wa
    @25
    @21
    cz
    wcel
    #
    wa
    #
    @28
    cP
    crp
    wcel
    #
    wa
    #
    @23
    @39
    @7
    @41
    @23
    @7
    @25
    @40
    @32
    neg1z
    jctir
    adantr
    @7
    @43
    @23
    @0
    @28
    @2
    @42
    @29
    @2
    @14
    @42
    @15
    @14
    cP
    @16
    nnrpd
    syl
    anim12i
    adantr
    @7
    @23
    simpr
    @9
    @21
    c2
    cP
    modexp
    syl3anc
    ex
    @7
    @39
    c2
    @5
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    wceq
    #
    @24
    @7
    @36
    @45
    @38
    c1
    @7
    @35
    @44
    cP
    cmo
    @7
    c2
    @8
    c2
    cmul
    co
    #
    cexp
    co
    #
    @35
    @44
    @7
    c2
    cc
    wcel
    #
    @8
    cn0
    wcel
    #
    @28
    w3a
    #
    @48
    @35
    wceq
    @0
    @51
    @2
    @0
    @49
    @50
    @28
    @0
    2cnd
    @30
    @29
    3jca
    adantr
    c2
    @8
    c2
    expmul
    syl
    @7
    @47
    @5
    c2
    cexp
    @7
    @5
    @47
    @7
    c2
    cN
    @7
    2cnd
    @0
    @18
    @2
    @19
    adantr
    expp1d
    eqcomd
    oveq2d
    eqtr3d
    oveq1d
    @7
    @38
    c1
    cP
    cmo
    co
    #
    c1
    @7
    @37
    c1
    cP
    cmo
    @37
    c1
    wceq
    @7
    neg1sqe1
    a1i
    oveq1d
    @2
    @52
    c1
    wceq
    #
    @0
    @2
    cP
    cr
    wcel
    c1
    cP
    clt
    wbr
    #
    @53
    @2
    cP
    @17
    nnred
    @2
    @14
    @54
    @15
    cP
    prmgt1
    syl
    cP
    1mod
    syl2anc
    adantl
    eqtrd
    eqeq12d
    @7
    @46
    @24
    @7
    @46
    wa
    #
    @11
    @6
    @55
    @11
    wa
    @7
    @20
    c1
    wne
    #
    @46
    @6
    @7
    @46
    @11
    simpll
    @55
    @11
    @56
    @55
    @11
    @23
    @56
    @55
    @25
    @26
    @12
    w3a
    #
    @27
    @7
    @57
    @46
    @2
    @0
    @14
    @57
    @15
    @0
    @14
    wa
    #
    @25
    @26
    @12
    @0
    @25
    @14
    @31
    adantr
    @58
    1zzd
    @14
    @12
    @0
    @16
    adantl
    3jca
    sylan2
    adantr
    @34
    syl
    @55
    @23
    @56
    @55
    @23
    wa
    #
    @56
    @22
    c1
    wne
    #
    @55
    @60
    @23
    @7
    @60
    @46
    @7
    @22
    cP
    c1
    cmin
    co
    #
    c1
    @7
    @12
    @22
    @61
    wceq
    @33
    cP
    m1modnnsub1
    syl
    @7
    @61
    c1
    wne
    c2
    cP
    wne
    @7
    cP
    c2
    @2
    cP
    c2
    wne
    @0
    cP
    cprime
    c2
    eldifsni
    adantl
    necomd
    @7
    @61
    c1
    c2
    cP
    @7
    @61
    c1
    wceq
    c1
    c1
    caddc
    co
    #
    cP
    wceq
    c2
    cP
    wceq
    @7
    cP
    c1
    c1
    @2
    cP
    cc
    wcel
    @0
    @2
    cP
    @17
    nncnd
    adantl
    @7
    1cnd
    #
    @63
    subadd2d
    @62
    c2
    cP
    1p1e2
    eqeq1i
    syl6bb
    necon3bid
    mpbird
    eqnetrd
    adantr
    adantr
    @59
    @20
    c1
    @22
    c1
    @23
    @20
    c1
    wceq
    @22
    c1
    wceq
    wb
    @55
    @20
    @22
    c1
    eqeq1
    adantl
    necon3bid
    mpbird
    ex
    sylbid
    imp
    @7
    @46
    @11
    simplr
    cP
    cN
    odz2prm2pw
    syl12anc
    ex
    ex
    sylbid
    syld
    sylbid
    pm2.43d
    syld
    3impia
end
