include "c2.mm"
include "wceq.mm"
include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "breq1.mm"
include "adantr.mm"
include "wn.mm"
include "cn0.mm"
include "nnnn0.mm"
include "fmtnoodd.mm"
include "syl.mm"
include "adantl.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "a1d.mm"
include "ex.mm"
include "3impd.mm"
include "codz.mm"
include "csn.mm"
include "cdif.mm"
include "simpr1.mm"
include "wne.mm"
include "neqne.mm"
include "anim2i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "3ad2ant2.mm"
include "impcom.mm"
include "simpr3.mm"
include "fmtnoprmfac1lem.mm"
include "syl3anc.mm"
include "cphi.mm"
include "cz.mm"
include "cgcd.mm"
include "prmnn.mm"
include "ad2antll.mm"
include "2z.mm"
include "a1i.mm"
include "necomd.mm"
include "2prm.mm"
include "anim1i.mm"
include "prmrp.mm"
include "mpbird.mm"
include "odzphi.mm"
include "cmin.mm"
include "phiprm.mm"
include "breq2d.mm"
include "2nn.mm"
include "peano2nn.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "cle.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzle.mm"
include "nn0ge2m1nn.mm"
include "syl2anc.mm"
include "anim12i.mm"
include "nndivides.mm"
include "eqcom.mm"
include "cc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "nncn.mm"
include "peano2nn0.mm"
include "mulcld.mm"
include "subadd2d.mm"
include "adantll.mm"
include "3bitrd.mm"
include "rexbidva.mm"
include "biimpd.mm"
include "com23.mm"
include "mpd.mm"
include "3adantr3.mm"
include "pm2.61i.mm"

theorem fmtnoprmfac1
  let cP: class P
  let vk: setvar k
  let cN: class N
  let vx: setvar x

  disjoint N k
  disjoint P k
  disjoint k x
  assert |- ( ( N e. NN /\ P e. Prime /\ P || ( FermatNo ` N ) ) -> E. k e. NN P = ( ( k x. ( 2 ^ ( N + 1 ) ) ) + 1 ) )

  proof
    cP
    c2
    wceq
    #
    cN
    cn
    wcel
    #
    cP
    cprime
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
    w3a
    #
    cP
    vk
    cv
    #
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn
    wrex
    #
    wi
    @0
    @1
    @2
    @4
    @12
    @0
    @1
    @2
    @4
    @12
    wi
    #
    wi
    @0
    @1
    wa
    #
    @13
    @2
    @14
    @4
    c2
    @3
    cdvds
    wbr
    #
    @12
    @0
    @4
    @15
    wb
    @1
    cP
    c2
    @3
    cdvds
    breq1
    adantr
    @14
    @15
    @12
    @1
    @15
    wn
    #
    @0
    @1
    cN
    cn0
    wcel
    #
    @16
    cN
    nnnn0
    #
    cN
    fmtnoodd
    syl
    adantl
    pm2.21d
    sylbid
    a1d
    ex
    3impd
    @0
    wn
    #
    @5
    @12
    @19
    @5
    wa
    #
    c2
    cP
    codz
    cfv
    cfv
    #
    @8
    wceq
    #
    @12
    @20
    @1
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @4
    @22
    @19
    @1
    @2
    @4
    simpr1
    @5
    @19
    @23
    @2
    @1
    @19
    @23
    wi
    @4
    @2
    @19
    @23
    @2
    @19
    wa
    @2
    cP
    c2
    wne
    #
    wa
    @23
    @19
    @24
    @2
    cP
    c2
    neqne
    #
    anim2i
    cP
    cprime
    c2
    eldifsn
    sylibr
    ex
    3ad2ant2
    impcom
    @19
    @1
    @2
    @4
    simpr3
    cP
    cN
    fmtnoprmfac1lem
    syl3anc
    @19
    @1
    @2
    @22
    @12
    wi
    #
    @4
    @19
    @1
    @2
    wa
    #
    wa
    #
    @21
    cP
    cphi
    cfv
    #
    cdvds
    wbr
    #
    @26
    @28
    cP
    cn
    wcel
    #
    c2
    cz
    wcel
    #
    c2
    cP
    cgcd
    co
    c1
    wceq
    #
    @30
    @2
    @31
    @19
    @1
    cP
    prmnn
    #
    ad2antll
    @32
    @28
    2z
    a1i
    @28
    @33
    c2
    cP
    wne
    #
    @19
    @35
    @27
    @19
    cP
    c2
    @25
    necomd
    adantr
    @28
    c2
    cprime
    wcel
    #
    @2
    wa
    #
    @33
    @35
    wb
    @27
    @37
    @19
    @1
    @36
    @2
    @36
    @1
    2prm
    a1i
    anim1i
    adantl
    c2
    cP
    prmrp
    syl
    mpbird
    c2
    cP
    odzphi
    syl3anc
    @28
    @30
    @21
    cP
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    @26
    @28
    @29
    @38
    @21
    cdvds
    @2
    @29
    @38
    wceq
    @19
    @1
    cP
    phiprm
    ad2antll
    breq2d
    @28
    @22
    @39
    @12
    @28
    @22
    @39
    @12
    wi
    @28
    @22
    wa
    @39
    @8
    @38
    cdvds
    wbr
    #
    @12
    @22
    @39
    @40
    wb
    @28
    @21
    @8
    @38
    cdvds
    breq1
    adantl
    @28
    @40
    @12
    wi
    @22
    @28
    @40
    @9
    @38
    wceq
    #
    vk
    cn
    wrex
    #
    @12
    @28
    @8
    cn
    wcel
    #
    @38
    cn
    wcel
    #
    wa
    #
    @40
    @42
    wb
    @27
    @45
    @19
    @1
    @43
    @2
    @44
    @1
    c2
    @7
    c2
    cn
    wcel
    @1
    2nn
    a1i
    #
    @1
    @7
    cN
    peano2nn
    nnnn0d
    nnexpcld
    @2
    cP
    cn0
    wcel
    c2
    cP
    cle
    wbr
    #
    @44
    @2
    cP
    @34
    nnnn0d
    @2
    cP
    c2
    cuz
    cfv
    wcel
    @47
    cP
    prmuz2
    c2
    cP
    eluzle
    syl
    cP
    nn0ge2m1nn
    syl2anc
    anim12i
    adantl
    vk
    @8
    @38
    nndivides
    syl
    @28
    @42
    @12
    @28
    @41
    @11
    vk
    cn
    @28
    @6
    cn
    wcel
    #
    wa
    #
    @41
    @38
    @9
    wceq
    #
    @10
    cP
    wceq
    #
    @11
    @41
    @50
    wb
    @49
    @9
    @38
    eqcom
    a1i
    @27
    @48
    @50
    @51
    wb
    @19
    @27
    @48
    wa
    #
    cP
    c1
    @9
    @27
    cP
    cc
    wcel
    #
    @48
    @2
    @53
    @1
    @2
    cP
    @34
    nncnd
    adantl
    adantr
    @52
    1cnd
    @52
    @6
    @8
    @48
    @6
    cc
    wcel
    @27
    @6
    nncn
    adantl
    @27
    @8
    cc
    wcel
    #
    @48
    @1
    @54
    @2
    @1
    @8
    @1
    c2
    @7
    @46
    @1
    @17
    @7
    cn0
    wcel
    @18
    cN
    peano2nn0
    syl
    nnexpcld
    nncnd
    adantr
    adantr
    mulcld
    subadd2d
    adantll
    @51
    @11
    wb
    @49
    @10
    cP
    eqcom
    a1i
    3bitrd
    rexbidva
    biimpd
    sylbid
    adantr
    sylbid
    ex
    com23
    sylbid
    mpd
    3adantr3
    mpd
    ex
    pm2.61i
end
