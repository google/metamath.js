include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "wa.mm"
include "clsw.mm"
include "cfzo.mm"
include "wb.mm"
include "cn.mm"
include "wi.mm"
include "cn0.mm"
include "cz.mm"
include "lencl.mm"
include "nn0z.mm"
include "elnnz.mm"
include "simplbi2.mm"
include "3syl.mm"
include "a1d.mm"
include "3imp.mm"
include "fzo0end.mm"
include "syl.mm"
include "2swrdeqwrdeq.mm"
include "syld3an3.mm"
include "cs1.mm"
include "c0.mm"
include "wne.mm"
include "hashneq0.mm"
include "biimpd.mm"
include "imdistani.mm"
include "3adant2.mm"
include "adantr.mm"
include "swrdlsw.mm"
include "breq2.mm"
include "3anbi3d.mm"
include "3adant1.mm"
include "syl6bi.mm"
include "impcom.mm"
include "oveq1.mm"
include "id.mm"
include "opeq12d.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "mpbird.mm"
include "eqeq12d.mm"
include "hashgt0n0.mm"
include "lswcl.mm"
include "syldan.mm"
include "s111.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "pm5.32da.mm"

theorem 2swrd1eqwrdeq
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ U e. Word V /\ 0 < ( # ` W ) ) -> ( W = U <-> ( ( # ` W ) = ( # ` U ) /\ ( ( W substr <. 0 , ( ( # ` W ) - 1 ) >. ) = ( U substr <. 0 , ( ( # ` W ) - 1 ) >. ) /\ ( lastS ` W ) = ( lastS ` U ) ) ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cc0
    cW
    chash
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    cW
    cU
    wceq
    #
    @3
    cU
    chash
    cfv
    #
    wceq
    #
    cW
    cc0
    @3
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    cU
    @10
    csubstr
    co
    wceq
    #
    cW
    @9
    @3
    cop
    #
    csubstr
    co
    #
    cU
    @12
    csubstr
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    @8
    @11
    cW
    clsw
    cfv
    #
    cU
    clsw
    cfv
    #
    wceq
    #
    wa
    #
    wa
    @1
    @2
    @4
    @9
    cc0
    @3
    cfzo
    co
    wcel
    #
    @6
    @17
    wb
    @5
    @3
    cn
    wcel
    #
    @22
    @1
    @2
    @4
    @23
    @1
    @4
    @23
    wi
    #
    @2
    @1
    @3
    cn0
    wcel
    @3
    cz
    wcel
    #
    @24
    cV
    cW
    lencl
    @3
    nn0z
    @23
    @25
    @4
    @3
    elnnz
    simplbi2
    3syl
    a1d
    3imp
    @3
    fzo0end
    syl
    cU
    @9
    cV
    cW
    2swrdeqwrdeq
    syld3an3
    @5
    @8
    @16
    @21
    @5
    @8
    wa
    #
    @15
    @20
    @11
    @26
    @15
    @18
    cs1
    #
    @19
    cs1
    #
    wceq
    #
    @20
    @26
    @13
    @27
    @14
    @28
    @26
    @1
    cW
    c0
    wne
    #
    wa
    #
    @13
    @27
    wceq
    @5
    @31
    @8
    @1
    @4
    @31
    @2
    @1
    @4
    @30
    @1
    @4
    @30
    cW
    @0
    hashneq0
    biimpd
    imdistani
    3adant2
    adantr
    cV
    cW
    swrdlsw
    syl
    @26
    @14
    @28
    wceq
    #
    cU
    @7
    c1
    cmin
    co
    #
    @7
    cop
    #
    csubstr
    co
    #
    @28
    wceq
    #
    @8
    @5
    @36
    @8
    @5
    @1
    @2
    cc0
    @7
    clt
    wbr
    #
    w3a
    #
    @36
    @8
    @4
    @37
    @1
    @2
    @3
    @7
    cc0
    clt
    breq2
    3anbi3d
    #
    @38
    @2
    cU
    c0
    wne
    #
    wa
    #
    @36
    @2
    @37
    @41
    @1
    @2
    @37
    @40
    @2
    @37
    @40
    cU
    @0
    hashneq0
    biimpd
    imdistani
    3adant1
    cV
    cU
    swrdlsw
    syl
    syl6bi
    impcom
    @8
    @32
    @36
    wb
    @5
    @8
    @14
    @35
    @28
    @8
    @12
    @34
    cU
    csubstr
    @8
    @9
    @33
    @3
    @7
    @3
    @7
    c1
    cmin
    oveq1
    @8
    id
    opeq12d
    oveq2d
    eqeq1d
    adantl
    mpbird
    eqeq12d
    @26
    @18
    cV
    wcel
    #
    @19
    cV
    wcel
    #
    @29
    @20
    wb
    @5
    @42
    @8
    @1
    @4
    @42
    @2
    @1
    @4
    @30
    @42
    cW
    @0
    hashgt0n0
    cV
    cW
    lswcl
    syldan
    3adant2
    adantr
    @8
    @5
    @43
    @8
    @5
    @38
    @43
    @39
    @2
    @37
    @43
    @1
    @2
    @37
    @40
    @43
    cU
    @0
    hashgt0n0
    cV
    cU
    lswcl
    syldan
    3adant1
    syl6bi
    impcom
    cV
    @18
    @19
    s111
    syl2anc
    bitrd
    anbi2d
    pm5.32da
    bitrd
end
