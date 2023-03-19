include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "ccsh.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "wi.mm"
include "c0.mm"
include "ral0.mm"
include "oveq2.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "a1d.mm"
include "wn.mm"
include "cmul.mm"
include "caddc.mm"
include "cmo.mm"
include "cn0.mm"
include "simprl.mm"
include "lencl.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "1nn0.mm"
include "a1i.mm"
include "wne.mm"
include "df-ne.mm"
include "elnnne0.mm"
include "simplbi2com.mm"
include "sylbir.mm"
include "adantr.mm"
include "impcom.mm"
include "biimpri.mm"
include "ad2antll.mm"
include "wb.mm"
include "nngt1ne1.mm"
include "syl.mm"
include "mpbird.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "simprr.mm"
include "lbfzo0.mm"
include "syl5bir.mm"
include "com12.mm"
include "imp.mm"
include "cz.mm"
include "elfzoelz.mm"
include "cshweqrep.mm"
include "sylan2.mm"
include "syl22anc.mm"
include "wss.mm"
include "0nn0.mm"
include "fzossnn0.mm"
include "ssralv.mm"
include "mp2b.mm"
include "eqcom.mm"
include "cr.mm"
include "zre.mm"
include "ax-1rid.mm"
include "oveq2d.mm"
include "zcn.mm"
include "addid2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "zmodidfzoimp.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "ralimia.mm"
include "impancom.mm"
include "csn.mm"
include "eqid.mm"
include "c0ex.mm"
include "fveq2.mm"
include "ralsn.mm"
include "mpbir.mm"
include "fzo01.mm"
include "pm2.61d2.mm"
include "pm2.61i.mm"

theorem cshw1
  let vi: setvar i
  let cV: class V
  let cW: class W

  disjoint V i
  disjoint W i
  assert |- ( ( W e. Word V /\ ( W cyclShift 1 ) = W ) -> A. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) = ( W ` 0 ) )

  proof
    cW
    chash
    cfv
    #
    cc0
    wceq
    #
    cW
    cV
    cword
    wcel
    #
    cW
    c1
    ccsh
    co
    cW
    wceq
    #
    wa
    #
    vi
    cv
    #
    cW
    cfv
    #
    cc0
    cW
    cfv
    #
    wceq
    #
    vi
    cc0
    @0
    cfzo
    co
    #
    wral
    #
    wi
    @1
    @10
    @4
    @1
    @10
    @8
    vi
    c0
    wral
    @8
    vi
    ral0
    @1
    @8
    vi
    @9
    c0
    @1
    @9
    cc0
    cc0
    cfzo
    co
    c0
    @0
    cc0
    cc0
    cfzo
    oveq2
    cc0
    fzo0
    syl6eq
    raleqdv
    mpbiri
    a1d
    @1
    wn
    #
    @4
    @10
    @11
    @4
    wa
    @0
    c1
    wceq
    #
    @10
    @11
    @12
    wn
    #
    @4
    @10
    @11
    @13
    wa
    #
    @4
    @10
    @14
    @4
    wa
    #
    @7
    cc0
    @5
    c1
    cmul
    co
    #
    caddc
    co
    #
    @0
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    vi
    cn0
    wral
    #
    @10
    @15
    @2
    c1
    @9
    wcel
    #
    @3
    cc0
    @9
    wcel
    #
    @21
    @14
    @2
    @3
    simprl
    @4
    @14
    @22
    @2
    @14
    @22
    wi
    #
    @3
    @2
    @0
    cn0
    wcel
    #
    @24
    cV
    cW
    lencl
    #
    @25
    @14
    @22
    @25
    @14
    wa
    #
    c1
    cn0
    wcel
    #
    @0
    cn
    wcel
    #
    c1
    @0
    clt
    wbr
    #
    @22
    @28
    @27
    1nn0
    a1i
    @14
    @25
    @29
    @11
    @25
    @29
    wi
    #
    @13
    @11
    @0
    cc0
    wne
    #
    @31
    @0
    cc0
    df-ne
    #
    @29
    @25
    @32
    @0
    elnnne0
    #
    simplbi2com
    sylbir
    adantr
    impcom
    #
    @27
    @30
    @0
    c1
    wne
    #
    @13
    @36
    @25
    @11
    @36
    @13
    @0
    c1
    df-ne
    biimpri
    ad2antll
    @27
    @29
    @30
    @36
    wb
    @35
    @0
    nngt1ne1
    syl
    mpbird
    c1
    @0
    elfzo0
    syl3anbrc
    ex
    syl
    adantr
    impcom
    @14
    @2
    @3
    simprr
    @14
    @4
    @23
    @11
    @4
    @23
    wi
    @13
    @4
    @11
    @23
    @2
    @11
    @23
    wi
    #
    @3
    @2
    @25
    @37
    @26
    @11
    @32
    @25
    @23
    @33
    @25
    @32
    @23
    @25
    @32
    wa
    @29
    @23
    @34
    @23
    @29
    @0
    lbfzo0
    biimpri
    sylbir
    ex
    syl5bir
    syl
    adantr
    com12
    adantr
    imp
    @2
    @22
    wa
    @3
    @23
    wa
    #
    @21
    @22
    @2
    c1
    cz
    wcel
    @38
    @21
    wi
    c1
    cc0
    @0
    elfzoelz
    vi
    cc0
    c1
    cV
    cW
    cshweqrep
    sylan2
    imp
    syl22anc
    @21
    @20
    vi
    @9
    wral
    #
    @10
    cc0
    cn0
    wcel
    @9
    cn0
    wss
    @21
    @39
    wi
    0nn0
    cc0
    @0
    fzossnn0
    @20
    vi
    @9
    cn0
    ssralv
    mp2b
    @20
    @8
    vi
    @9
    @20
    @19
    @7
    wceq
    #
    @5
    @9
    wcel
    #
    @8
    @7
    @19
    eqcom
    @41
    @40
    @8
    @41
    @19
    @6
    @7
    @41
    @18
    @5
    cW
    @41
    @18
    @5
    @0
    cmo
    co
    @5
    @41
    @17
    @5
    @0
    cmo
    @41
    @5
    cz
    wcel
    #
    @17
    @5
    wceq
    @5
    cc0
    @0
    elfzoelz
    @42
    @17
    cc0
    @5
    caddc
    co
    @5
    @42
    @16
    @5
    cc0
    caddc
    @42
    @5
    cr
    wcel
    @16
    @5
    wceq
    @5
    zre
    @5
    ax-1rid
    syl
    oveq2d
    @42
    @5
    @5
    zcn
    addid2d
    eqtrd
    syl
    oveq1d
    @5
    @0
    zmodidfzoimp
    eqtrd
    fveq2d
    eqeq1d
    biimpd
    syl5bi
    ralimia
    syl
    syl
    ex
    impancom
    @12
    @10
    @8
    vi
    cc0
    csn
    #
    wral
    #
    @44
    @7
    @7
    wceq
    #
    @7
    eqid
    @8
    @45
    vi
    cc0
    c0ex
    @5
    cc0
    wceq
    @6
    @7
    @7
    @5
    cc0
    cW
    fveq2
    eqeq1d
    ralsn
    mpbir
    @12
    @8
    vi
    @9
    @43
    @12
    @9
    cc0
    c1
    cfzo
    co
    @43
    @0
    c1
    cc0
    cfzo
    oveq2
    fzo01
    syl6eq
    raleqdv
    mpbiri
    pm2.61d2
    ex
    pm2.61i
end
