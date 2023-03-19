include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "wa.mm"
include "clsw.mm"
include "cfzo.mm"
include "wb.mm"
include "cn0.mm"
include "lencl.mm"
include "cn.mm"
include "cle.mm"
include "caddc.mm"
include "cz.mm"
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
include "simpl.mm"
include "nn0sub.mm"
include "mpbid.mm"
include "adantr.mm"
include "cr.mm"
include "wi.mm"
include "0red.mm"
include "1red.mm"
include "nn0re.mm"
include "3jca.mm"
include "0lt1.mm"
include "lttr.mm"
include "expd.mm"
include "mpisyl.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "2pos.mm"
include "2re.mm"
include "ltsubposd.mm"
include "mpbii.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "sylan.mm"
include "3adant2.mm"
include "2swrdeqwrdeq.mm"
include "syld3an3.mm"
include "cs2.mm"
include "cs1.mm"
include "swrd2lsw.mm"
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
include "s2eq2s1eq.mm"
include "syl22anc.mm"
include "fvex.mm"
include "s111.mm"
include "fveq2d.mm"
include "eqcoms.mm"
include "eqeq2d.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "3bitrd.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"

theorem 2swrd2eqwrdeq
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ U e. Word V /\ 1 < ( # ` W ) ) -> ( W = U <-> ( ( # ` W ) = ( # ` U ) /\ ( ( W substr <. 0 , ( ( # ` W ) - 2 ) >. ) = ( U substr <. 0 , ( ( # ` W ) - 2 ) >. ) /\ ( W ` ( ( # ` W ) - 2 ) ) = ( U ` ( ( # ` W ) - 2 ) ) /\ ( lastS ` W ) = ( lastS ` U ) ) ) ) )

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
    c1
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
    c2
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
    @9
    cW
    cfv
    #
    @9
    cU
    cfv
    #
    wceq
    #
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
    w3a
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
    @1
    @4
    @25
    @2
    @1
    @3
    cn0
    wcel
    #
    @4
    @25
    cV
    cW
    lencl
    @26
    @4
    wa
    #
    @9
    cn0
    wcel
    #
    @3
    cn
    wcel
    #
    @9
    @3
    clt
    wbr
    #
    @25
    @27
    c2
    @3
    cle
    wbr
    #
    @28
    @26
    @4
    @31
    @26
    @4
    c1
    c1
    caddc
    co
    #
    @3
    cle
    wbr
    #
    @31
    @26
    c1
    cz
    wcel
    @3
    cz
    wcel
    #
    @4
    @33
    wb
    1z
    @3
    nn0z
    #
    c1
    @3
    zltp1le
    sylancr
    @26
    @33
    @31
    @26
    @32
    c2
    @3
    cle
    @32
    c2
    wceq
    @26
    1p1e2
    a1i
    breq1d
    biimpd
    sylbid
    imp
    @27
    c2
    cn0
    wcel
    @26
    @31
    @28
    wb
    2nn0
    @26
    @4
    simpl
    c2
    @3
    nn0sub
    sylancr
    mpbid
    @27
    @34
    cc0
    @3
    clt
    wbr
    #
    @29
    @26
    @34
    @4
    @35
    adantr
    @26
    @4
    @36
    @26
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @3
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
    @4
    @36
    wi
    @26
    @37
    @38
    @39
    @26
    0red
    @26
    1red
    @3
    nn0re
    #
    3jca
    0lt1
    @40
    @41
    @4
    @36
    cc0
    c1
    @3
    lttr
    expd
    mpisyl
    imp
    @3
    elnnz
    sylanbrc
    @26
    @30
    @4
    @26
    cc0
    c2
    clt
    wbr
    @30
    2pos
    @26
    c2
    @3
    c2
    cr
    wcel
    @26
    2re
    a1i
    @42
    ltsubposd
    mpbii
    adantr
    @9
    @3
    elfzo0
    syl3anbrc
    sylan
    3adant2
    cU
    @9
    cV
    cW
    2swrdeqwrdeq
    syld3an3
    @5
    @8
    @16
    @24
    @5
    @8
    wa
    #
    @16
    @11
    @20
    @23
    wa
    #
    wa
    @24
    @43
    @15
    @44
    @11
    @43
    @15
    @18
    @21
    cs2
    #
    @7
    c2
    cmin
    co
    #
    cU
    cfv
    #
    @22
    cs2
    #
    wceq
    #
    @18
    cs1
    @47
    cs1
    wceq
    #
    @21
    cs1
    @22
    cs1
    wceq
    #
    wa
    #
    @44
    @43
    @13
    @45
    @14
    @48
    @5
    @13
    @45
    wceq
    #
    @8
    @1
    @4
    @53
    @2
    cV
    cW
    swrd2lsw
    3adant2
    adantr
    @43
    @14
    @48
    wceq
    #
    cU
    @46
    @7
    cop
    #
    csubstr
    co
    #
    @48
    wceq
    #
    @8
    @5
    @57
    @8
    @5
    @1
    @2
    c1
    @7
    clt
    wbr
    #
    w3a
    @57
    @8
    @4
    @58
    @1
    @2
    @3
    @7
    c1
    clt
    breq2
    3anbi3d
    @2
    @58
    @57
    @1
    cV
    cU
    swrd2lsw
    3adant1
    syl6bi
    impcom
    @8
    @54
    @57
    wb
    @5
    @8
    @14
    @56
    @48
    @8
    @12
    @55
    cU
    csubstr
    @8
    @9
    @46
    @3
    @7
    @3
    @7
    c2
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
    @43
    @18
    cvv
    wcel
    #
    @21
    cvv
    wcel
    #
    @47
    cvv
    wcel
    #
    @22
    cvv
    wcel
    #
    @49
    @52
    wb
    @43
    @9
    cW
    fvexd
    @43
    cW
    clsw
    fvexd
    @43
    @46
    cU
    fvexd
    #
    @43
    cU
    clsw
    fvexd
    #
    @18
    @21
    @47
    @22
    cvv
    s2eq2s1eq
    syl22anc
    @43
    @50
    @20
    @51
    @23
    @43
    @50
    @18
    @47
    wceq
    #
    @20
    @43
    @59
    @61
    @50
    @65
    wb
    @9
    cW
    fvex
    @63
    cvv
    @18
    @47
    s111
    sylancr
    @43
    @47
    @19
    @18
    @8
    @47
    @19
    wceq
    #
    @5
    @66
    @7
    @3
    @7
    @3
    wceq
    @46
    @9
    cU
    @7
    @3
    c2
    cmin
    oveq1
    fveq2d
    eqcoms
    adantl
    eqeq2d
    bitrd
    @43
    @60
    @62
    @51
    @23
    wb
    cW
    clsw
    fvex
    @64
    cvv
    @21
    @22
    s111
    sylancr
    anbi12d
    3bitrd
    anbi2d
    @11
    @20
    @23
    3anass
    syl6bbr
    pm5.32da
    bitrd
end
