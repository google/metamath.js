include "cwwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cv.mm"
include "cwlks.mm"
include "wbr.mm"
include "wex.mm"
include "cvv.mm"
include "cvtx.mm"
include "cword.mm"
include "wa.mm"
include "wi.mm"
include "eqid.mm"
include "wwlkbp.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "iswwlks.mm"
include "ciedg.mm"
include "cdm.mm"
include "cfz.mm"
include "wf.mm"
include "wceq.mm"
include "ccnv.mm"
include "cmpt.mm"
include "ovex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "cle.mm"
include "crn.mm"
include "simprr.mm"
include "simplr.mm"
include "hashge1.mm"
include "ancoms.mm"
include "adantr.mm"
include "3jca.mm"
include "edgval.mm"
include "a1i.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "biimpd.mm"
include "wlkiswwlks2lem6.mm"
include "sylsyld.mm"
include "wb.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "imbi2d.mm"
include "adantl.mm"
include "mpbird.mm"
include "spcimedv.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "expd.mm"
include "impcom.mm"
include "imp.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "upgriswlk.mm"
include "syl.mm"
include "exbidv.mm"
include "syl5bi.mm"
include "mpcom.mm"
include "com12.mm"

theorem wlkiswwlks2
  let cP: class P
  let vf: setvar f
  let cG: class G
  let vi: setvar i
  let vx: setvar x

  disjoint G f
  disjoint P f
  disjoint G i
  disjoint G x
  disjoint f i
  disjoint f x
  disjoint i x
  disjoint P i
  disjoint P x
  assert |- ( G e. USPGraph -> ( P e. ( WWalks ` G ) -> E. f f ( Walks ` G ) P ) )

  proof
    cP
    cG
    cwwlks
    cfv
    wcel
    #
    cG
    cuspgr
    wcel
    #
    vf
    cv
    #
    cP
    cG
    cwlks
    cfv
    wbr
    #
    vf
    wex
    #
    cG
    cvv
    wcel
    cP
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    wa
    #
    @0
    @1
    @4
    wi
    #
    cG
    @5
    cP
    @5
    eqid
    #
    wwlkbp
    @0
    cP
    c0
    wne
    #
    @7
    vi
    cv
    #
    cP
    cfv
    @12
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vi
    cc0
    cP
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @8
    @9
    vi
    @14
    cG
    @5
    cP
    @10
    @14
    eqid
    iswwlks
    @8
    @20
    @9
    @8
    @20
    wa
    #
    @1
    @4
    @21
    @1
    wa
    #
    @4
    @2
    cG
    ciedg
    cfv
    #
    cdm
    cword
    #
    wcel
    #
    cc0
    @2
    chash
    cfv
    #
    cfz
    co
    #
    @5
    cP
    wf
    #
    @12
    @2
    cfv
    #
    @23
    cfv
    #
    @13
    wceq
    #
    vi
    cc0
    @26
    cfzo
    co
    #
    wral
    #
    w3a
    #
    vf
    wex
    #
    @21
    @1
    @35
    @20
    @8
    @1
    @35
    wi
    @20
    @8
    @1
    @35
    @11
    @7
    @19
    @8
    @1
    wa
    #
    @35
    wi
    @11
    @7
    wa
    #
    @36
    @19
    @35
    @37
    @36
    @19
    @35
    wi
    @37
    @36
    wa
    #
    @34
    @19
    vf
    vx
    @18
    vx
    cv
    #
    cP
    cfv
    @39
    c1
    caddc
    co
    cP
    cfv
    cpr
    @23
    ccnv
    cfv
    #
    cmpt
    #
    cvv
    @18
    cvv
    wcel
    @41
    cvv
    wcel
    @38
    cc0
    @17
    cfzo
    ovex
    vx
    @18
    @40
    cvv
    mptexg
    mp1i
    @38
    @2
    @41
    wceq
    #
    wa
    #
    @19
    @34
    wi
    #
    @19
    @41
    @24
    wcel
    #
    cc0
    @41
    chash
    cfv
    #
    cfz
    co
    #
    @5
    cP
    wf
    #
    @12
    @41
    cfv
    #
    @23
    cfv
    #
    @13
    wceq
    #
    vi
    cc0
    @46
    cfzo
    co
    #
    wral
    #
    w3a
    #
    wi
    #
    @43
    @1
    @7
    c1
    @16
    cle
    wbr
    #
    w3a
    #
    @19
    @13
    @23
    crn
    #
    wcel
    #
    vi
    @18
    wral
    #
    @54
    @38
    @57
    @42
    @38
    @1
    @7
    @56
    @37
    @8
    @1
    simprr
    @11
    @7
    @36
    simplr
    @37
    @56
    @36
    @7
    @11
    @56
    cP
    @6
    hashge1
    ancoms
    adantr
    3jca
    adantr
    @43
    @19
    @60
    @43
    @15
    @59
    vi
    @18
    @43
    @14
    @58
    @13
    @14
    @58
    wceq
    @43
    cG
    edgval
    a1i
    eleq2d
    ralbidv
    biimpd
    vx
    cP
    vi
    @23
    @41
    cG
    @5
    @41
    eqid
    @23
    eqid
    #
    wlkiswwlks2lem6
    sylsyld
    @42
    @44
    @55
    wb
    @38
    @42
    @34
    @54
    @19
    @42
    @25
    @45
    @28
    @48
    @33
    @53
    @2
    @41
    @24
    eleq1
    @42
    @27
    @47
    @5
    cP
    @42
    @26
    @46
    cc0
    cfz
    @2
    @41
    chash
    fveq2
    #
    oveq2d
    feq2d
    @42
    @31
    @51
    vi
    @32
    @52
    @42
    @26
    @46
    cc0
    cfzo
    @62
    oveq2d
    @42
    @30
    @50
    @13
    @42
    @29
    @49
    @23
    @12
    @2
    @41
    fveq1
    fveq2d
    eqeq1d
    raleqbidv
    3anbi123d
    imbi2d
    adantl
    mpbird
    spcimedv
    ex
    com23
    3impia
    expd
    impcom
    imp
    @22
    @3
    @34
    vf
    @1
    @3
    @34
    wb
    #
    @21
    @1
    cG
    cupgr
    wcel
    @63
    cG
    uspgrupgr
    cP
    vi
    @2
    cG
    @23
    @5
    @10
    @61
    upgriswlk
    syl
    adantl
    exbidv
    mpbird
    ex
    ex
    syl5bi
    mpcom
    com12
end
