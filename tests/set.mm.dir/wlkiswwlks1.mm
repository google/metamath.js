include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cwwlks.mm"
include "wlkn0.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "upgriswlk.mm"
include "wa.mm"
include "cedg.mm"
include "cmin.mm"
include "simpr.mm"
include "ffz0iswrd.mm"
include "3ad2ant2.mm"
include "ad2antlr.mm"
include "crn.mm"
include "wfn.mm"
include "cuhgr.mm"
include "wfun.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "funfn.mm"
include "biimpi.mm"
include "3syl.mm"
include "wrdsymbcl.mm"
include "ad4ant14.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "edgval.mm"
include "syl6eleqr.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibrcom.mm"
include "ralimdva.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "impcom.mm"
include "cn0.mm"
include "lencl.mm"
include "ffz0hash.mm"
include "oveq1.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "syld.mm"
include "imp.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "3adant3.mm"
include "adantl.mm"
include "mpbird.mm"
include "adantr.mm"
include "iswwlks.mm"
include "syl3anbrc.mm"
include "sylbid.mm"
include "mpdi.mm"

theorem wlkiswwlks1
  let cP: class P
  let cF: class F
  let cG: class G
  let vi: setvar i


  assert |- ( G e. UPGraph -> ( F ( Walks ` G ) P -> P e. ( WWalks ` G ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cP
    c0
    wne
    #
    cP
    cG
    cwwlks
    cfv
    wcel
    #
    cP
    cF
    cG
    wlkn0
    @0
    @1
    cF
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
    cF
    chash
    cfv
    #
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    vi
    cv
    #
    cF
    cfv
    #
    @4
    cfv
    #
    @10
    cP
    cfv
    @10
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    wceq
    #
    vi
    cc0
    @7
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @2
    @3
    wi
    #
    cP
    vi
    cF
    cG
    @4
    @8
    @8
    eqid
    #
    @4
    eqid
    #
    upgriswlk
    @0
    @17
    @18
    @0
    @17
    wa
    #
    @2
    @3
    @21
    @2
    wa
    @2
    cP
    @8
    cword
    wcel
    #
    @13
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
    @3
    @21
    @2
    simpr
    @17
    @22
    @0
    @2
    @9
    @6
    @22
    @16
    @8
    @7
    cP
    ffz0iswrd
    3ad2ant2
    ad2antlr
    @21
    @28
    @2
    @21
    @28
    @24
    vi
    @15
    wral
    #
    @17
    @0
    @29
    @6
    @9
    @16
    @0
    @29
    wi
    @6
    @9
    wa
    #
    @0
    @16
    @29
    @30
    @0
    @16
    @29
    wi
    @30
    @0
    wa
    #
    @14
    @24
    vi
    @15
    @31
    @10
    @15
    wcel
    #
    wa
    #
    @24
    @14
    @12
    @23
    wcel
    #
    @33
    @12
    @4
    crn
    #
    @23
    @33
    @4
    @5
    wfn
    #
    @11
    @5
    wcel
    #
    @12
    @35
    wcel
    @0
    @36
    @30
    @32
    @0
    cG
    cuhgr
    wcel
    @4
    wfun
    #
    @36
    cG
    upgruhgr
    @4
    cG
    @20
    uhgrfun
    @38
    @36
    @4
    funfn
    biimpi
    3syl
    ad2antlr
    @6
    @32
    @37
    @9
    @0
    @10
    @5
    cF
    wrdsymbcl
    ad4ant14
    @5
    @11
    @4
    fnfvelrn
    syl2anc
    cG
    edgval
    syl6eleqr
    @24
    @34
    wb
    @13
    @12
    @13
    @12
    @23
    eleq1
    eqcoms
    syl5ibrcom
    ralimdva
    ex
    com23
    3impia
    impcom
    @17
    @28
    @29
    wb
    #
    @0
    @6
    @9
    @39
    @16
    @30
    @24
    vi
    @27
    @15
    @30
    @26
    @7
    cc0
    cfzo
    @6
    @9
    @26
    @7
    wceq
    #
    @6
    @7
    cn0
    wcel
    #
    @9
    @40
    wi
    @5
    cF
    lencl
    @41
    @9
    @25
    @7
    c1
    caddc
    co
    #
    wceq
    #
    @40
    @41
    @9
    @43
    @8
    cP
    @7
    ffz0hash
    ex
    @41
    @43
    @40
    @43
    @41
    @26
    @42
    c1
    cmin
    co
    #
    @7
    @25
    @42
    c1
    cmin
    oveq1
    @41
    @7
    cc
    wcel
    @44
    @7
    wceq
    @7
    nn0cn
    @7
    pncan1
    syl
    sylan9eqr
    ex
    syld
    syl
    imp
    oveq2d
    raleqdv
    3adant3
    adantl
    mpbird
    adantr
    vi
    @23
    cG
    @8
    cP
    @19
    @23
    eqid
    iswwlks
    syl3anbrc
    ex
    ex
    sylbid
    mpdi
end
