include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "cs2.mm"
include "clsw.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "w3a.mm"
include "wceq.mm"
include "simpl.mm"
include "lencl.mm"
include "cle.mm"
include "cz.mm"
include "wb.mm"
include "1z.mm"
include "nn0z.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "1p1e2.mm"
include "a1i.mm"
include "breq1d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "imp.mm"
include "2nn0.mm"
include "jctl.mm"
include "adantr.mm"
include "nn0sub.mm"
include "syl.mm"
include "mpbid.mm"
include "sylan.mm"
include "cn.mm"
include "wi.mm"
include "cr.mm"
include "0red.mm"
include "1red.mm"
include "zre.mm"
include "3jca.mm"
include "0lt1.mm"
include "lttr.mm"
include "expd.mm"
include "mpisyl.mm"
include "elnnz.mm"
include "simplbi2.mm"
include "syld.mm"
include "fzo0end.mm"
include "cc.mm"
include "nn0cn.mm"
include "2cn.mm"
include "1cnd.mm"
include "1e2m1.mm"
include "oveq2d.mm"
include "subsub.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "swrds2.mm"
include "jctir.mm"
include "npcan.mm"
include "3syl.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "lsw.mm"
include "2m1e1.mm"
include "fveq2d.mm"
include "s2eqd.mm"
include "3eqtr4d.mm"

theorem swrd2lsw
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ 1 < ( # ` W ) ) -> ( W substr <. ( ( # ` W ) - 2 ) , ( # ` W ) >. ) = <" ( W ` ( ( # ` W ) - 2 ) ) ( lastS ` W ) "> )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    c1
    cW
    chash
    cfv
    #
    clt
    wbr
    #
    wa
    #
    cW
    @2
    c2
    cmin
    co
    #
    @5
    c2
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    @5
    cW
    cfv
    #
    @5
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cs2
    #
    cW
    @5
    @2
    cop
    #
    csubstr
    co
    @9
    cW
    clsw
    cfv
    #
    cs2
    @4
    @1
    @5
    cn0
    wcel
    #
    @10
    cc0
    @2
    cfzo
    co
    #
    wcel
    #
    w3a
    @8
    @12
    wceq
    @4
    @1
    @15
    @17
    @1
    @3
    simpl
    @1
    @2
    cn0
    wcel
    #
    @3
    @15
    cV
    cW
    lencl
    #
    @18
    @3
    wa
    #
    c2
    @2
    cle
    wbr
    #
    @15
    @18
    @3
    @21
    @18
    @3
    c1
    c1
    caddc
    co
    #
    @2
    cle
    wbr
    #
    @21
    @18
    c1
    cz
    wcel
    @2
    cz
    wcel
    #
    @3
    @23
    wb
    1z
    @2
    nn0z
    #
    c1
    @2
    zltp1le
    sylancr
    @18
    @23
    @21
    @18
    @22
    c2
    @2
    cle
    @22
    c2
    wceq
    @18
    1p1e2
    a1i
    breq1d
    biimpd
    sylbid
    imp
    @20
    c2
    cn0
    wcel
    #
    @18
    wa
    #
    @21
    @15
    wb
    @18
    @27
    @3
    @18
    @26
    2nn0
    jctl
    adantr
    c2
    @2
    nn0sub
    syl
    mpbid
    sylan
    @1
    @18
    @3
    @17
    @19
    @20
    @17
    @2
    c1
    cmin
    co
    #
    @16
    wcel
    #
    @20
    @2
    cn
    wcel
    #
    @29
    @18
    @3
    @30
    @18
    @24
    @3
    @30
    wi
    @25
    @24
    @3
    cc0
    @2
    clt
    wbr
    #
    @30
    @24
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    w3a
    #
    cc0
    c1
    clt
    wbr
    #
    @3
    @31
    wi
    @24
    @32
    @33
    @34
    @24
    0red
    @24
    1red
    @2
    zre
    3jca
    0lt1
    @35
    @36
    @3
    @31
    cc0
    c1
    @2
    lttr
    expd
    mpisyl
    @30
    @24
    @31
    @2
    elnnz
    simplbi2
    syld
    syl
    imp
    @2
    fzo0end
    syl
    @18
    @17
    @29
    wb
    @3
    @18
    @10
    @28
    @16
    @18
    @28
    @10
    @18
    @2
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    w3a
    #
    @28
    @10
    wceq
    @18
    @37
    @38
    @39
    @2
    nn0cn
    #
    @38
    @18
    2cn
    a1i
    @18
    1cnd
    3jca
    #
    @40
    @28
    @2
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @10
    @40
    c1
    @43
    @2
    cmin
    c1
    @43
    wceq
    @40
    1e2m1
    a1i
    oveq2d
    @2
    c2
    c1
    subsub
    #
    eqtrd
    syl
    eqcomd
    eleq1d
    adantr
    mpbird
    sylan
    3jca
    cV
    @5
    cW
    swrds2
    syl
    @4
    @13
    @7
    cW
    csubstr
    @4
    @2
    @6
    @5
    @1
    @2
    @6
    wceq
    #
    @3
    @1
    @18
    @37
    @38
    wa
    #
    @46
    @19
    @18
    @37
    @38
    @41
    2cn
    jctir
    @47
    @6
    @2
    @2
    c2
    npcan
    eqcomd
    3syl
    adantr
    opeq2d
    oveq2d
    @4
    @9
    @14
    @9
    @11
    @4
    @9
    eqidd
    @1
    @14
    @11
    wceq
    @3
    @1
    @14
    @28
    cW
    cfv
    @11
    cW
    @0
    lsw
    @1
    @28
    @10
    cW
    @1
    @10
    @28
    @1
    @18
    @10
    @28
    wceq
    @19
    @18
    @10
    @44
    @28
    @18
    @44
    @10
    @18
    @40
    @44
    @10
    wceq
    @42
    @45
    syl
    eqcomd
    @18
    @43
    c1
    @2
    cmin
    @43
    c1
    wceq
    @18
    2m1e1
    a1i
    oveq2d
    eqtrd
    syl
    eqcomd
    fveq2d
    eqtrd
    adantr
    s2eqd
    3eqtr4d
end
