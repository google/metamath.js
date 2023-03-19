include "c2.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "c8.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "wcel.mm"
include "wb.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cneg.mm"
include "cexp.mm"
include "cmin.mm"
include "cdiv.mm"
include "eldifi.mm"
include "2lgs.mm"
include "syl.mm"
include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "cdvds.mm"
include "wbr.mm"
include "eqcom.mm"
include "a1i.mm"
include "cz.mm"
include "wn.mm"
include "cn.mm"
include "nnoddn2prm.mm"
include "nnz.mm"
include "anim1i.mm"
include "sqoddm1div8z.mm"
include "m1exp1.mm"
include "2lgsoddprmlem4.mm"
include "3bitrd.mm"
include "biimparc.mm"
include "adantl.mm"
include "eqtrd.mm"
include "exp32.mm"
include "cc0.mm"
include "ctp.mm"
include "2z.mm"
include "prmz.mm"
include "lgscl1.mm"
include "sylancr.mm"
include "w3o.mm"
include "ovex.mm"
include "eltp.mm"
include "notbid.mm"
include "biimpar.mm"
include "m1expo.mm"
include "syl2an2r.mm"
include "eqcomd.mm"
include "a1d.mm"
include "wne.mm"
include "cgcd.mm"
include "eldifsn.mm"
include "simpr.mm"
include "necomd.mm"
include "sylbi.mm"
include "2prm.mm"
include "prmrp.mm"
include "mpbird.mm"
include "lgsne0.mm"
include "eqneqall.mm"
include "syl5.mm"
include "pm2.24.mm"
include "2a1d.mm"
include "3jaoi.mm"
include "mpcom.mm"
include "com13.mm"
include "bija.mm"

theorem 2lgsoddprm
  let cP: class P


  assert |- ( P e. ( Prime \ { 2 } ) -> ( 2 /L P ) = ( -u 1 ^ ( ( ( P ^ 2 ) - 1 ) / 8 ) ) )

  proof
    c2
    cP
    clgs
    co
    #
    c1
    wceq
    #
    cP
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    #
    wb
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @0
    c1
    cneg
    #
    cP
    c2
    cexp
    co
    c1
    cmin
    co
    c8
    cdiv
    co
    #
    cexp
    co
    #
    wceq
    #
    @5
    cP
    cprime
    wcel
    #
    @3
    cP
    cprime
    @4
    eldifi
    #
    cP
    2lgs
    syl
    @1
    @2
    @5
    @9
    wi
    @1
    @2
    @5
    @9
    @1
    @2
    @5
    wa
    #
    wa
    @0
    c1
    @8
    @1
    @12
    simpl
    @12
    c1
    @8
    wceq
    #
    @1
    @5
    @13
    @2
    @5
    @13
    @8
    c1
    wceq
    #
    c2
    @7
    cdvds
    wbr
    #
    @2
    @13
    @14
    wb
    @5
    c1
    @8
    eqcom
    a1i
    @5
    @7
    cz
    wcel
    #
    @14
    @15
    wb
    @5
    cP
    cz
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    @16
    @5
    cP
    cn
    wcel
    #
    @18
    wa
    @19
    cP
    nnoddn2prm
    @20
    @17
    @18
    cP
    nnz
    anim1i
    syl
    #
    cP
    sqoddm1div8z
    syl
    #
    @7
    m1exp1
    syl
    @5
    @19
    @15
    @2
    wb
    @21
    cP
    2lgsoddprmlem4
    syl
    #
    3bitrd
    biimparc
    adantl
    eqtrd
    exp32
    @5
    @2
    wn
    #
    @1
    wn
    #
    @9
    @0
    @6
    cc0
    c1
    ctp
    wcel
    #
    @5
    @24
    @25
    @9
    wi
    #
    wi
    #
    @5
    c2
    cz
    wcel
    #
    @17
    @26
    2z
    @5
    @10
    @17
    @11
    cP
    prmz
    syl
    #
    c2
    cP
    lgscl1
    sylancr
    @26
    @0
    @6
    wceq
    #
    @0
    cc0
    wceq
    #
    @1
    w3o
    @5
    @28
    wi
    #
    @0
    @6
    cc0
    c1
    c2
    cP
    clgs
    ovex
    eltp
    @31
    @33
    @32
    @1
    @31
    @5
    @24
    @27
    @31
    @5
    @24
    wa
    #
    wa
    #
    @9
    @25
    @35
    @0
    @6
    @8
    @31
    @34
    simpl
    @34
    @6
    @8
    wceq
    @31
    @34
    @8
    @6
    @5
    @16
    @24
    @15
    wn
    #
    @8
    @6
    wceq
    @22
    @5
    @36
    @24
    @5
    @15
    @2
    @23
    notbid
    biimpar
    @7
    m1expo
    syl2an2r
    eqcomd
    adantl
    eqtrd
    a1d
    exp32
    @5
    @0
    cc0
    wne
    #
    @32
    @28
    @5
    @37
    c2
    cP
    cgcd
    co
    c1
    wceq
    #
    @5
    @38
    c2
    cP
    wne
    #
    @5
    @10
    cP
    c2
    wne
    #
    wa
    #
    @39
    cP
    cprime
    c2
    eldifsn
    @41
    cP
    c2
    @10
    @40
    simpr
    necomd
    sylbi
    @5
    c2
    cprime
    wcel
    @10
    @38
    @39
    wb
    2prm
    @11
    c2
    cP
    prmrp
    sylancr
    mpbird
    @5
    @29
    @17
    @37
    @38
    wb
    2z
    @30
    c2
    cP
    lgsne0
    sylancr
    mpbird
    @28
    @0
    cc0
    eqneqall
    syl5
    @1
    @27
    @5
    @24
    @1
    @9
    pm2.24
    2a1d
    3jaoi
    sylbi
    mpcom
    com13
    bija
    mpcom
end
