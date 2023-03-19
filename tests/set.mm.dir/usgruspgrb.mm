include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cedg.mm"
include "wral.mm"
include "wa.mm"
include "usgruspgr.mm"
include "cvtx.mm"
include "cpw.mm"
include "edgusgr.mm"
include "simprd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "wf1.mm"
include "crn.mm"
include "edgval.mm"
include "a1i.mm"
include "raleqdv.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wi.mm"
include "eqid.mm"
include "uspgrf.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "ssel2.mm"
include "expcom.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "breq1d.mm"
include "elrab.mm"
include "eldifi.mm"
include "anim1i.mm"
include "sylibr.mm"
include "ex.mm"
include "adantr.mm"
include "sylbi.mm"
include "syl9.mm"
include "syld.mm"
include "com13.mm"
include "imp.mm"
include "ssrdv.mm"
include "mpan9.mm"
include "f1ssr.mm"
include "syldan.mm"
include "sylbid.mm"
include "wb.mm"
include "isusgrs.mm"
include "mpbird.mm"
include "impbii.mm"

theorem usgruspgrb
  let ve: setvar e
  let cG: class G
  let vx: setvar x
  let vy: setvar y

  disjoint G e
  disjoint G x
  disjoint G y
  disjoint e x
  disjoint e y
  disjoint x y
  assert |- ( G e. USGraph <-> ( G e. USPGraph /\ A. e e. ( Edg ` G ) ( # ` e ) = 2 ) )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cuspgr
    wcel
    #
    ve
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    ve
    cG
    cedg
    cfv
    #
    wral
    #
    wa
    #
    @0
    @1
    @6
    cG
    usgruspgr
    @0
    @4
    ve
    @5
    @0
    @2
    @5
    wcel
    wa
    @2
    cG
    cvtx
    cfv
    #
    cpw
    #
    wcel
    @4
    @2
    cG
    edgusgr
    simprd
    ralrimiva
    jca
    @7
    @0
    cG
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    @9
    crab
    #
    @10
    wf1
    #
    @1
    @6
    @16
    @1
    @6
    @4
    ve
    @10
    crn
    #
    wral
    #
    @16
    @1
    @4
    ve
    @5
    @17
    @5
    @17
    wceq
    @1
    cG
    edgval
    a1i
    raleqdv
    @1
    @11
    @13
    c2
    cle
    wbr
    #
    vx
    @9
    c0
    csn
    #
    cdif
    #
    crab
    #
    @10
    wf1
    #
    @18
    @16
    wi
    vx
    @10
    cG
    @8
    @8
    eqid
    #
    @10
    eqid
    #
    uspgrf
    @23
    @18
    @16
    @23
    @18
    @17
    @15
    wss
    #
    @16
    @23
    @17
    @22
    wss
    #
    @18
    @26
    @23
    @11
    @22
    @10
    wf
    @27
    @11
    @22
    @10
    f1f
    @11
    @22
    @10
    frn
    syl
    @18
    @27
    @26
    @18
    @27
    wa
    vy
    @17
    @15
    @18
    @27
    vy
    cv
    #
    @17
    wcel
    #
    @28
    @15
    wcel
    #
    wi
    @29
    @27
    @18
    @30
    @29
    @27
    @28
    @22
    wcel
    #
    @18
    @30
    wi
    @27
    @29
    @31
    @17
    @22
    @28
    ssel2
    expcom
    @29
    @18
    @28
    chash
    cfv
    #
    c2
    wceq
    #
    @31
    @30
    @4
    @33
    ve
    @28
    @17
    ve
    vy
    weq
    @3
    @32
    c2
    @2
    @28
    chash
    fveq2
    eqeq1d
    rspcv
    @31
    @28
    @21
    wcel
    #
    @32
    c2
    cle
    wbr
    #
    wa
    @33
    @30
    wi
    #
    @19
    @35
    vx
    @28
    @21
    vx
    vy
    weq
    #
    @13
    @32
    c2
    cle
    @12
    @28
    chash
    fveq2
    #
    breq1d
    elrab
    @34
    @36
    @35
    @34
    @33
    @30
    @34
    @33
    wa
    @28
    @9
    wcel
    #
    @33
    wa
    @30
    @34
    @39
    @33
    @28
    @9
    @20
    eldifi
    anim1i
    @14
    @33
    vx
    @28
    @9
    @37
    @13
    @32
    c2
    @38
    eqeq1d
    elrab
    sylibr
    ex
    adantr
    sylbi
    syl9
    syld
    com13
    imp
    ssrdv
    ex
    mpan9
    @11
    @22
    @15
    @10
    f1ssr
    syldan
    ex
    syl
    sylbid
    imp
    @1
    @0
    @16
    wb
    @6
    vx
    cuspgr
    @10
    cG
    @8
    @24
    @25
    isusgrs
    adantr
    mpbird
    impbii
end
