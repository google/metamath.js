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
include "cpfx.mm"
include "cop.mm"
include "csubstr.mm"
include "wa.mm"
include "clsw.mm"
include "cfzo.mm"
include "wb.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "hashgt0n0.mm"
include "lennncl.mm"
include "syldan.mm"
include "3adant2.mm"
include "fzo0end.mm"
include "syl.mm"
include "pfxsuffeqwrdeq.mm"
include "syld3an3.mm"
include "cs1.mm"
include "hashneq0.mm"
include "biimpd.mm"
include "imdistani.mm"
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
include "cvv.mm"
include "fvexd.mm"
include "fvex.mm"
include "s111.mm"
include "sylancl.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "pm5.32da.mm"

theorem pfxsuff1eqwrdeq
  let cU: class U
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ U e. Word V /\ 0 < ( # ` W ) ) -> ( W = U <-> ( ( # ` W ) = ( # ` U ) /\ ( ( W prefix ( ( # ` W ) - 1 ) ) = ( U prefix ( ( # ` W ) - 1 ) ) /\ ( lastS ` W ) = ( lastS ` U ) ) ) ) )

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
    @3
    c1
    cmin
    co
    #
    cpfx
    co
    cU
    @9
    cpfx
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
    @11
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
    @10
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
    @16
    wb
    @5
    @3
    cn
    wcel
    #
    @21
    @1
    @4
    @22
    @2
    @1
    @4
    cW
    c0
    wne
    #
    @22
    cW
    @0
    hashgt0n0
    cV
    cW
    lennncl
    syldan
    3adant2
    @3
    fzo0end
    syl
    cU
    @9
    cV
    cW
    pfxsuffeqwrdeq
    syld3an3
    @5
    @8
    @15
    @20
    @5
    @8
    wa
    #
    @14
    @19
    @10
    @24
    @14
    @17
    cs1
    #
    @18
    cs1
    #
    wceq
    #
    @19
    @24
    @12
    @25
    @13
    @26
    @24
    @1
    @23
    wa
    #
    @12
    @25
    wceq
    @5
    @28
    @8
    @1
    @4
    @28
    @2
    @1
    @4
    @23
    @1
    @4
    @23
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
    @24
    @13
    @26
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
    @26
    wceq
    #
    @8
    @5
    @33
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
    @33
    @8
    @4
    @34
    @1
    @2
    @3
    @7
    cc0
    clt
    breq2
    3anbi3d
    @35
    @2
    cU
    c0
    wne
    #
    wa
    #
    @33
    @2
    @34
    @37
    @1
    @2
    @34
    @36
    @2
    @34
    @36
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
    @29
    @33
    wb
    @5
    @8
    @13
    @32
    @26
    @8
    @11
    @31
    cU
    csubstr
    @8
    @9
    @30
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
    @24
    @17
    cvv
    wcel
    @18
    cvv
    wcel
    @27
    @19
    wb
    @24
    cW
    clsw
    fvexd
    cU
    clsw
    fvex
    cvv
    @17
    @18
    s111
    sylancl
    bitrd
    anbi2d
    pm5.32da
    bitrd
end
