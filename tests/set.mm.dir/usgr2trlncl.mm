include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "ctrls.mm"
include "wbr.mm"
include "cc0.mm"
include "wne.mm"
include "wi.mm"
include "cfzo.mm"
include "co.mm"
include "ciedg.mm"
include "cdm.mm"
include "wf1.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "cupgr.mm"
include "wb.mm"
include "usgrupgr.mm"
include "eqid.mm"
include "upgrf1istrl.mm"
include "syl.mm"
include "wa.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "f1eq123d.mm"
include "raleqdv.mm"
include "2wlklem.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "adantl.mm"
include "cvv.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "0ne1.mm"
include "f12dfv.mm"
include "mp2an.mm"
include "cedg.mm"
include "wf1o.mm"
include "usgrf1oedg.mm"
include "f1of1.mm"
include "id.mm"
include "prid1.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "prid2.mm"
include "jca.mm"
include "anim2i.mm"
include "ancoms.mm"
include "f1veqaeq.mm"
include "necon3d.mm"
include "simpl.mm"
include "simpr.mm"
include "neeq12d.mm"
include "preq1.mm"
include "prcom.mm"
include "necon3i.mm"
include "syl6bi.mm"
include "com12.mm"
include "a1d.mm"
include "syl6.mm"
include "expcom.mm"
include "impd.mm"
include "com23.mm"
include "mpcom.mm"
include "syl5bi.mm"
include "adantr.mm"
include "sylbid.mm"
include "3adant2.mm"
include "expdcom.mm"
include "imp.mm"

theorem usgr2trlncl
  let cP: class P
  let cF: class F
  let cG: class G
  let vi: setvar i


  assert |- ( ( G e. USGraph /\ ( # ` F ) = 2 ) -> ( F ( Trails ` G ) P -> ( P ` 0 ) =/= ( P ` 2 ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    c2
    cP
    cfv
    #
    wne
    #
    wi
    @0
    @3
    @2
    @6
    @0
    @3
    cc0
    @1
    cfzo
    co
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    cF
    wf1
    #
    cc0
    @1
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
    @8
    cfv
    @13
    cP
    cfv
    @13
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    #
    vi
    @7
    wral
    #
    w3a
    #
    @2
    @6
    wi
    @0
    cG
    cupgr
    wcel
    @3
    @16
    wb
    cG
    usgrupgr
    cP
    vi
    cF
    cG
    @8
    @11
    @11
    eqid
    @8
    eqid
    #
    upgrf1istrl
    syl
    @0
    @2
    @16
    @6
    @16
    @0
    @2
    @6
    @10
    @15
    @0
    @2
    wa
    #
    @6
    wi
    @12
    @18
    @10
    @15
    wa
    #
    @6
    @18
    @19
    cc0
    c1
    cpr
    #
    @9
    cF
    wf1
    #
    cc0
    cF
    cfv
    #
    @8
    cfv
    #
    @4
    c1
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    c1
    cF
    cfv
    #
    @8
    cfv
    #
    @24
    @5
    cpr
    #
    wceq
    #
    wa
    #
    wa
    #
    @6
    @2
    @19
    @32
    wb
    @0
    @2
    @10
    @21
    @15
    @31
    @2
    @7
    @20
    @9
    @9
    cF
    cF
    @2
    cF
    eqidd
    @2
    @7
    cc0
    c2
    cfzo
    co
    @20
    @1
    c2
    cc0
    cfzo
    oveq2
    fzo0to2pr
    syl6eq
    #
    @2
    @9
    eqidd
    f1eq123d
    @2
    @15
    @14
    vi
    @20
    wral
    @31
    @2
    @14
    vi
    @7
    @20
    @33
    raleqdv
    cP
    vi
    @8
    cF
    2wlklem
    syl6bb
    anbi12d
    adantl
    @0
    @32
    @6
    wi
    @2
    @0
    @21
    @31
    @6
    @21
    @20
    @9
    cF
    wf
    #
    @22
    @27
    wne
    #
    wa
    #
    @0
    @31
    @6
    wi
    #
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    cc0
    c1
    wne
    @21
    @36
    wb
    @38
    @39
    c0ex
    1ex
    pm3.2i
    0ne1
    @20
    @9
    cvv
    cF
    cvv
    cc0
    c1
    @20
    eqid
    f12dfv
    mp2an
    @9
    cG
    cedg
    cfv
    #
    @8
    wf1o
    #
    @0
    @36
    @37
    wi
    #
    @40
    cG
    @8
    @17
    @40
    eqid
    usgrf1oedg
    @41
    @9
    @40
    @8
    wf1
    #
    @0
    @42
    wi
    @9
    @40
    @8
    f1of1
    @43
    @36
    @0
    @37
    @43
    @34
    @35
    @0
    @37
    wi
    #
    @34
    @43
    @35
    @44
    wi
    @34
    @43
    wa
    #
    @35
    @23
    @28
    wne
    #
    @44
    @45
    @23
    @28
    @22
    @27
    @45
    @43
    @22
    @9
    wcel
    #
    @27
    @9
    wcel
    #
    wa
    #
    wa
    #
    @23
    @28
    wceq
    @22
    @27
    wceq
    wi
    @43
    @34
    @50
    @34
    @49
    @43
    @34
    @47
    @48
    @34
    @20
    @9
    cc0
    cF
    @34
    id
    #
    cc0
    @20
    wcel
    @34
    cc0
    c1
    c0ex
    prid1
    a1i
    ffvelrnd
    @34
    @20
    @9
    c1
    cF
    @51
    c1
    @20
    wcel
    @34
    cc0
    c1
    1ex
    prid2
    a1i
    ffvelrnd
    jca
    anim2i
    ancoms
    @9
    @40
    @22
    @27
    @8
    f1veqaeq
    syl
    necon3d
    @46
    @37
    @0
    @31
    @46
    @6
    @31
    @46
    @25
    @29
    wne
    @6
    @31
    @23
    @25
    @28
    @29
    @26
    @30
    simpl
    @26
    @30
    simpr
    neeq12d
    @4
    @5
    @25
    @29
    @4
    @5
    wceq
    @25
    @5
    @24
    cpr
    @29
    @4
    @5
    @24
    preq1
    @5
    @24
    prcom
    syl6eq
    necon3i
    syl6bi
    com12
    a1d
    syl6
    expcom
    impd
    com23
    syl
    mpcom
    syl5bi
    impd
    adantr
    sylbid
    com12
    3adant2
    expdcom
    com23
    sylbid
    com23
    imp
end
