include "cwwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cvtx.mm"
include "cword.mm"
include "cv.mm"
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
include "cupgr.mm"
include "cwlks.mm"
include "wbr.mm"
include "wex.mm"
include "eqid.mm"
include "iswwlks.mm"
include "wa.mm"
include "ciedg.mm"
include "cdm.mm"
include "cfz.mm"
include "wf.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "crn.mm"
include "edgval.mm"
include "eleq2i.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "adantl.mm"
include "elrnrexdm.mm"
include "eqcom.mm"
include "rexbii.mm"
include "syl6ibr.mm"
include "syl5bi.mm"
include "ralimdv.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "impcom.mm"
include "ovex.mm"
include "fvex.mm"
include "dmex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ac6.mm"
include "iswrdi.mm"
include "adantr.mm"
include "cn.mm"
include "cfn.mm"
include "wb.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "bicomd.mm"
include "biimpac.mm"
include "wrdf.mm"
include "cz.mm"
include "nnz.mm"
include "fzoval.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "fnfzo0hash.mm"
include "sylan.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "feq2d.mm"
include "biimpcd.mm"
include "expd.mm"
include "mpd.mm"
include "3adant3.mm"
include "com12.mm"
include "simpr.mm"
include "imp.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "anasss.mm"
include "3jca.mm"
include "eximdv.mm"
include "upgriswlk.mm"
include "exbidv.mm"

theorem wlkiswwlksupgr2
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
  assert |- ( G e. UPGraph -> ( P e. ( WWalks ` G ) -> E. f f ( Walks ` G ) P ) )

  proof
    cP
    cG
    cwwlks
    cfv
    wcel
    cP
    c0
    wne
    #
    cP
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    vi
    cv
    #
    cP
    cfv
    @3
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
    cG
    cupgr
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
    vi
    @5
    cG
    @1
    cP
    @1
    eqid
    #
    @5
    eqid
    iswwlks
    @12
    @11
    @15
    @12
    @11
    wa
    #
    @15
    @13
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cc0
    @13
    chash
    cfv
    #
    cfz
    co
    #
    @1
    cP
    wf
    #
    @3
    @13
    cfv
    #
    @18
    cfv
    #
    @4
    wceq
    #
    vi
    cc0
    @21
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
    @17
    @9
    @19
    @13
    wf
    #
    @26
    vi
    @9
    wral
    #
    wa
    #
    vf
    wex
    #
    @30
    @17
    vx
    cv
    #
    @18
    cfv
    #
    @4
    wceq
    #
    vx
    @19
    wrex
    #
    vi
    @9
    wral
    #
    @34
    @11
    @12
    @39
    @0
    @2
    @10
    @12
    @39
    wi
    @0
    @2
    wa
    #
    @12
    @10
    @39
    @40
    @12
    @10
    @39
    wi
    @40
    @12
    wa
    #
    @6
    @38
    vi
    @9
    @6
    @4
    @18
    crn
    #
    wcel
    #
    @41
    @38
    @5
    @42
    @4
    cG
    edgval
    eleq2i
    @41
    @18
    wfun
    #
    @43
    @38
    wi
    @12
    @44
    @40
    @12
    cG
    cuhgr
    wcel
    @44
    cG
    upgruhgr
    @18
    cG
    @18
    eqid
    #
    uhgrfun
    syl
    adantl
    @44
    @43
    @4
    @36
    wceq
    #
    vx
    @19
    wrex
    @38
    vx
    @18
    @4
    elrnrexdm
    @37
    @46
    vx
    @19
    @36
    @4
    eqcom
    rexbii
    syl6ibr
    syl
    syl5bi
    ralimdv
    ex
    com23
    3impia
    impcom
    @37
    @26
    vi
    vx
    @9
    @19
    vf
    cc0
    @8
    cfzo
    ovex
    @18
    cG
    ciedg
    fvex
    dmex
    @35
    @24
    wceq
    @36
    @25
    @4
    @35
    @24
    @18
    fveq2
    eqeq1d
    ac6
    syl
    @17
    @33
    @29
    vf
    @17
    @33
    @29
    @17
    @33
    wa
    @20
    @23
    @28
    @33
    @20
    @17
    @31
    @20
    @32
    @19
    @8
    @13
    iswrdi
    adantr
    adantl
    @33
    @17
    @23
    @31
    @17
    @23
    wi
    @32
    @17
    @31
    @23
    @11
    @31
    @23
    wi
    #
    @12
    @0
    @2
    @47
    @10
    @40
    @7
    cn
    wcel
    #
    @47
    @2
    @0
    @48
    @2
    cP
    cfn
    wcel
    #
    @0
    @48
    wb
    @1
    cP
    wrdfin
    @49
    @48
    @0
    cP
    hashnncl
    bicomd
    syl
    biimpac
    #
    @2
    @48
    @47
    wi
    #
    @0
    @2
    cc0
    @7
    cfzo
    co
    #
    @1
    cP
    wf
    #
    @51
    @1
    cP
    wrdf
    @53
    @48
    @31
    @23
    @48
    @31
    wa
    #
    @53
    @23
    @54
    @52
    @22
    @1
    cP
    @54
    @52
    cc0
    @8
    cfz
    co
    #
    @22
    @48
    @52
    @55
    wceq
    #
    @31
    @48
    @7
    cz
    wcel
    @56
    @7
    nnz
    cc0
    @7
    fzoval
    syl
    adantr
    @54
    @8
    @21
    cc0
    cfz
    @54
    @21
    @8
    @48
    @8
    cn0
    wcel
    @31
    @21
    @8
    wceq
    #
    @7
    nnm1nn0
    @19
    @13
    @8
    fnfzo0hash
    sylan
    #
    eqcomd
    oveq2d
    eqtrd
    feq2d
    biimpcd
    expd
    syl
    adantl
    mpd
    3adant3
    adantl
    com12
    adantr
    impcom
    @17
    @31
    @32
    @28
    @17
    @31
    wa
    #
    @32
    wa
    #
    @28
    @32
    @59
    @32
    simpr
    @60
    @26
    vi
    @27
    @9
    @59
    @27
    @9
    wceq
    #
    @32
    @17
    @31
    @61
    @11
    @31
    @61
    wi
    #
    @12
    @0
    @2
    @62
    @10
    @40
    @31
    @61
    @40
    @31
    wa
    @21
    @8
    cc0
    cfzo
    @40
    @48
    @31
    @57
    @50
    @58
    sylan
    oveq2d
    ex
    3adant3
    adantl
    imp
    adantr
    raleqdv
    mpbird
    anasss
    3jca
    ex
    eximdv
    mpd
    @17
    @14
    @29
    vf
    @12
    @14
    @29
    wb
    @11
    cP
    vi
    @13
    cG
    @18
    @1
    @16
    @45
    upgriswlk
    adantr
    exbidv
    mpbird
    ex
    syl5bi
end
