include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "c1.mm"
include "wne.mm"
include "caddc.mm"
include "wceq.mm"
include "codz.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "cmin.mm"
include "cz.mm"
include "wb.mm"
include "eldifi.mm"
include "2nn.mm"
include "a1i.mm"
include "cn0.mm"
include "2nn0.mm"
include "peano2nn.mm"
include "nnnn0d.mm"
include "nn0expcld.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "modprm1div.mm"
include "syl2anr.mm"
include "cgcd.mm"
include "w3a.mm"
include "prmnn.mm"
include "syl.mm"
include "adantl.mm"
include "2z.mm"
include "eldifsn.mm"
include "simpr.mm"
include "necomd.mm"
include "sylbi.mm"
include "2prm.mm"
include "prmrp.mm"
include "sylancr.mm"
include "mpbird.mm"
include "3jca.mm"
include "adantr.mm"
include "odzdvds.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "wn.mm"
include "nnnn0.mm"
include "necon3abid.mm"
include "cv.mm"
include "cle.mm"
include "wrex.mm"
include "odzcl.mm"
include "dvdsprmpweqle.mm"
include "mp3an2i.mm"
include "breq1.mm"
include "notbid.mm"
include "clt.mm"
include "wo.mm"
include "cr.mm"
include "nn0re.mm"
include "nnred.mm"
include "leloe.mm"
include "cuz.mm"
include "nn0z.mm"
include "nnz.mm"
include "zleltp1.mm"
include "biimpar.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "dvdsexp.mm"
include "mp3an2ani.mm"
include "pm2.24d.mm"
include "expcom.mm"
include "oveq2.mm"
include "2a1d.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"
include "eqtrd.mm"
include "ex.mm"
include "expl.mm"
include "rexlimdva.mm"
include "syld.mm"
include "com23.mm"
include "imp32.mm"

theorem odz2prm2pw
  let cP: class P
  let cN: class N
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( N e. NN /\ P e. ( Prime \ { 2 } ) ) /\ ( ( ( 2 ^ ( 2 ^ N ) ) mod P ) =/= 1 /\ ( ( 2 ^ ( 2 ^ ( N + 1 ) ) ) mod P ) = 1 ) ) -> ( ( odZ ` P ) ` 2 ) = ( 2 ^ ( N + 1 ) ) )

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
    wa
    #
    c2
    c2
    cN
    cexp
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    wne
    #
    c2
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    c1
    wceq
    #
    c2
    cP
    codz
    cfv
    cfv
    #
    @9
    wceq
    #
    @3
    @11
    @7
    @13
    @3
    @11
    @12
    @9
    cdvds
    wbr
    #
    @7
    @13
    wi
    @3
    @11
    cP
    @10
    c1
    cmin
    co
    cdvds
    wbr
    #
    @14
    @2
    cP
    cprime
    wcel
    #
    @10
    cz
    wcel
    @11
    @15
    wb
    @0
    cP
    cprime
    @1
    eldifi
    #
    @0
    @10
    @0
    c2
    @9
    c2
    cn
    wcel
    @0
    2nn
    a1i
    #
    @0
    c2
    @8
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    #
    @0
    @8
    cN
    peano2nn
    #
    nnnn0d
    #
    nn0expcld
    #
    nnexpcld
    nnzd
    @10
    cP
    modprm1div
    syl2anr
    @3
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
    w3a
    #
    @9
    cn0
    wcel
    #
    @15
    @14
    wb
    @3
    @23
    @24
    @25
    @2
    @23
    @0
    @2
    @16
    @23
    @17
    cP
    prmnn
    syl
    adantl
    @24
    @3
    2z
    a1i
    @2
    @25
    @0
    @2
    @25
    c2
    cP
    wne
    #
    @2
    @16
    cP
    c2
    wne
    #
    wa
    #
    @28
    cP
    cprime
    c2
    eldifsn
    @30
    cP
    c2
    @16
    @29
    simpr
    necomd
    sylbi
    @2
    c2
    cprime
    wcel
    #
    @16
    @25
    @28
    wb
    2prm
    @17
    c2
    cP
    prmrp
    sylancr
    mpbird
    adantl
    3jca
    #
    @0
    @27
    @2
    @22
    adantr
    c2
    @9
    cP
    odzdvds
    syl2anc
    bitrd
    @3
    @7
    @14
    @13
    @3
    @7
    @12
    @4
    cdvds
    wbr
    #
    wn
    #
    @14
    @13
    wi
    @3
    @33
    @6
    c1
    @3
    @6
    c1
    wceq
    #
    cP
    @5
    c1
    cmin
    co
    cdvds
    wbr
    #
    @33
    @2
    @16
    @5
    cz
    wcel
    @35
    @36
    wb
    @0
    @17
    @0
    @5
    @0
    c2
    @4
    @18
    @0
    c2
    cN
    @19
    cN
    nnnn0
    nn0expcld
    #
    nnexpcld
    nnzd
    @5
    cP
    modprm1div
    syl2anr
    @3
    @26
    @4
    cn0
    wcel
    #
    @36
    @33
    wb
    @32
    @0
    @38
    @2
    @37
    adantr
    c2
    @4
    cP
    odzdvds
    syl2anc
    bitrd
    necon3abid
    @3
    @14
    @34
    @13
    @3
    @14
    vn
    cv
    #
    @8
    cle
    wbr
    #
    @12
    c2
    @39
    cexp
    co
    #
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    #
    @34
    @13
    wi
    #
    @31
    @3
    @12
    cn
    wcel
    #
    @8
    cn0
    wcel
    #
    @14
    @44
    wi
    2prm
    @3
    @26
    @46
    @32
    c2
    cP
    odzcl
    syl
    @0
    @47
    @2
    @21
    adantr
    @12
    c2
    vn
    @8
    dvdsprmpweqle
    mp3an2i
    @3
    @43
    @45
    vn
    cn0
    @3
    @39
    cn0
    wcel
    #
    wa
    #
    @40
    @42
    @45
    @49
    @40
    wa
    #
    @42
    wa
    #
    @34
    @41
    @4
    cdvds
    wbr
    #
    wn
    #
    @13
    @51
    @33
    @52
    @42
    @33
    @52
    wb
    @50
    @12
    @41
    @4
    cdvds
    breq1
    adantl
    notbid
    @51
    @53
    @13
    @51
    @53
    wa
    @12
    @41
    @9
    @51
    @42
    @53
    @50
    @42
    simpr
    adantr
    @51
    @53
    @41
    @9
    wceq
    #
    @50
    @53
    @54
    wi
    #
    @42
    @49
    @40
    @55
    @49
    @40
    @39
    @8
    clt
    wbr
    #
    @39
    @8
    wceq
    #
    wo
    #
    @55
    @48
    @39
    cr
    wcel
    @8
    cr
    wcel
    #
    @40
    @58
    wb
    @3
    @39
    nn0re
    @0
    @59
    @2
    @0
    @8
    @20
    nnred
    adantr
    @39
    @8
    leloe
    syl2anr
    @58
    @49
    @55
    @56
    @49
    @55
    wi
    @57
    @49
    @56
    @55
    @49
    @56
    wa
    #
    @52
    @54
    @24
    @49
    @48
    @56
    cN
    @39
    cuz
    cfv
    wcel
    #
    @52
    2z
    @3
    @48
    simpr
    @60
    @39
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @39
    cN
    cle
    wbr
    #
    @61
    @49
    @62
    @56
    @48
    @62
    @3
    @39
    nn0z
    #
    adantl
    adantr
    @49
    @63
    @56
    @3
    @63
    @48
    @0
    @63
    @2
    cN
    nnz
    adantr
    #
    adantr
    adantr
    @49
    @64
    @56
    @48
    @62
    @63
    @64
    @56
    wb
    @3
    @65
    @66
    @39
    cN
    zleltp1
    syl2anr
    biimpar
    @39
    cN
    eluz2
    syl3anbrc
    c2
    @39
    cN
    dvdsexp
    mp3an2ani
    pm2.24d
    expcom
    @57
    @54
    @49
    @53
    @39
    @8
    c2
    cexp
    oveq2
    2a1d
    jaoi
    com12
    sylbid
    imp
    adantr
    imp
    eqtrd
    ex
    sylbid
    expl
    rexlimdva
    syld
    com23
    sylbid
    com23
    sylbid
    com23
    imp32
end
