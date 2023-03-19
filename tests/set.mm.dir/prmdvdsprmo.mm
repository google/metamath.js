include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cprmo.mm"
include "cfv.mm"
include "cdvds.mm"
include "wi.mm"
include "cprime.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cif.mm"
include "cprod.mm"
include "cmul.mm"
include "cz.mm"
include "cfn.mm"
include "fzfi.mm"
include "diffi.mm"
include "mp1i.mm"
include "eldifi.mm"
include "elfzelz.mm"
include "syl.mm"
include "1zzd.mm"
include "ifcld.mm"
include "adantl.mm"
include "fprodzcl.mm"
include "prmz.mm"
include "adantr.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cn0.mm"
include "nnnn0.mm"
include "prmoval.mm"
include "ad2antrr.mm"
include "breq2d.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "neldifsnd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cun.mm"
include "prmnn.mm"
include "anim1i.mm"
include "wb.mm"
include "nnz.mm"
include "fznn.mm"
include "mpbird.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "fzfid.mm"
include "cc.mm"
include "zcnd.mm"
include "fprodsplit.mm"
include "simplr.mm"
include "nncnd.mm"
include "1cnd.mm"
include "eleq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "prodsn.mm"
include "simpr.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "bitrd.mm"
include "ex.mm"
include "ralrimiva.mm"

theorem prmdvdsprmo
  let cN: class N
  let vp: setvar p
  let vk: setvar k

  disjoint N p
  disjoint N k
  disjoint k p
  assert |- ( N e. NN -> A. p e. Prime ( p <_ N -> p || ( #p ` N ) ) )

  proof
    cN
    cn
    wcel
    #
    vp
    cv
    #
    cN
    cle
    wbr
    #
    @1
    cN
    cprmo
    cfv
    #
    cdvds
    wbr
    #
    wi
    vp
    cprime
    @0
    @1
    cprime
    wcel
    #
    wa
    #
    @2
    @4
    @6
    @2
    wa
    #
    @4
    @1
    c1
    cN
    cfz
    co
    #
    @1
    csn
    #
    cdif
    #
    vk
    cv
    #
    cprime
    wcel
    #
    @11
    c1
    cif
    #
    vk
    cprod
    #
    @1
    cmul
    co
    #
    cdvds
    wbr
    #
    @7
    @14
    cz
    wcel
    @1
    cz
    wcel
    #
    @16
    @7
    @10
    @13
    vk
    @8
    cfn
    wcel
    @10
    cfn
    wcel
    @7
    c1
    cN
    fzfi
    @8
    @9
    diffi
    mp1i
    @11
    @10
    wcel
    #
    @13
    cz
    wcel
    @7
    @18
    @12
    @11
    c1
    cz
    @18
    @11
    @8
    wcel
    #
    @11
    cz
    wcel
    @11
    @8
    @9
    eldifi
    @11
    c1
    cN
    elfzelz
    #
    syl
    @18
    1zzd
    ifcld
    adantl
    fprodzcl
    @6
    @17
    @2
    @5
    @17
    @0
    @1
    prmz
    adantl
    adantr
    @14
    @1
    dvdsmul2
    syl2anc
    @7
    @4
    @1
    @8
    @13
    vk
    cprod
    #
    cdvds
    wbr
    @16
    @7
    @3
    @21
    @1
    cdvds
    @0
    @3
    @21
    wceq
    #
    @5
    @2
    @0
    cN
    cn0
    wcel
    @22
    cN
    nnnn0
    vk
    cN
    prmoval
    syl
    ad2antrr
    breq2d
    @7
    @21
    @15
    @1
    cdvds
    @7
    @21
    @14
    @9
    @13
    vk
    cprod
    #
    cmul
    co
    @15
    @7
    @10
    @9
    @13
    @8
    vk
    @7
    @1
    @10
    wcel
    wn
    @10
    @9
    cin
    c0
    wceq
    @7
    @1
    @8
    neldifsnd
    @10
    @1
    disjsn
    sylibr
    @7
    @1
    @8
    wcel
    #
    @8
    @10
    @9
    cun
    #
    wceq
    @7
    @24
    @1
    cn
    wcel
    #
    @2
    wa
    #
    @6
    @26
    @2
    @5
    @26
    @0
    @1
    prmnn
    adantl
    #
    anim1i
    @0
    @24
    @27
    wb
    #
    @5
    @2
    @0
    cN
    cz
    wcel
    @29
    cN
    nnz
    @1
    cN
    fznn
    syl
    ad2antrr
    mpbird
    @24
    @25
    @8
    @8
    @1
    difsnid
    eqcomd
    syl
    @7
    c1
    cN
    fzfid
    @19
    @13
    cc
    wcel
    @7
    @19
    @13
    @19
    @12
    @11
    c1
    cz
    @20
    @19
    1zzd
    ifcld
    zcnd
    adantl
    fprodsplit
    @7
    @23
    @1
    @14
    cmul
    @7
    @23
    @5
    @1
    c1
    cif
    #
    @1
    @7
    @5
    @30
    cc
    wcel
    @23
    @30
    wceq
    @0
    @5
    @2
    simplr
    @7
    @5
    @1
    c1
    cc
    @7
    @1
    @6
    @26
    @2
    @28
    adantr
    nncnd
    @7
    1cnd
    ifcld
    @13
    @30
    vk
    @1
    cprime
    @11
    @1
    wceq
    #
    @12
    @5
    @11
    @1
    c1
    @11
    @1
    cprime
    eleq1
    @31
    id
    ifbieq1d
    prodsn
    syl2anc
    @6
    @30
    @1
    wceq
    @2
    @6
    @5
    @1
    c1
    @0
    @5
    simpr
    iftrued
    adantr
    eqtrd
    oveq2d
    eqtrd
    breq2d
    bitrd
    mpbird
    ex
    ralrimiva
end
