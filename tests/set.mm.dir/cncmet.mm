include "cc.mm"
include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "wtru.mm"
include "c1.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "eqid.mm"
include "cnfldtopn.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "cme.mm"
include "cnmet.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crp.mm"
include "1rp.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "ccl.mm"
include "crest.mm"
include "ccmp.mm"
include "ccld.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "ctop.mm"
include "wss.mm"
include "cnfldtop.mm"
include "cxmt.mm"
include "cxr.mm"
include "metxmet.mm"
include "ax-mp.mm"
include "rpxr.mm"
include "blssm.mm"
include "mp3an13.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "clscld.mm"
include "sylancr.mm"
include "caddc.mm"
include "abscl.mm"
include "peano2re.mm"
include "syl.mm"
include "cab.mm"
include "wa.mm"
include "crab.mm"
include "df-rab.mm"
include "eqcomi.mm"
include "blcls.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "resubcld.mm"
include "simpl.mm"
include "id.mm"
include "subcl.mm"
include "syl2anr.mm"
include "abscld.mm"
include "1red.mm"
include "simprl.mm"
include "abs2difd.mm"
include "wceq.mm"
include "cnmetdval.mm"
include "abssub.mm"
include "eqtrd.mm"
include "adantrr.mm"
include "simprr.mm"
include "eqbrtrrd.mm"
include "letrd.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "ex.mm"
include "ss2abdv.mm"
include "sstrd.mm"
include "ssabral.mm"
include "sylib.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "clsss3.mm"
include "cnheibor.mm"
include "mpbir2and.mm"
include "adantl.mm"
include "relcmpcmet.mm"
include "trud.mm"

theorem cncmet
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume cncmet.1: |- D = ( abs o. - )


  assert |- D e. ( CMet ` CC )

  proof
    cD
    cc
    cms
    cfv
    wcel
    wtru
    vx
    cD
    c1
    ccnfld
    ctopn
    cfv
    #
    cc
    @0
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    cD
    cmopn
    cfv
    @0
    @0
    eqid
    #
    cnfldtopn
    cD
    @1
    cmopn
    cncmet.1
    fveq2i
    eqtr4i
    #
    cD
    cc
    cme
    cfv
    #
    wcel
    #
    wtru
    cD
    @1
    @4
    cncmet.1
    cnmet
    eqeltri
    #
    a1i
    c1
    crp
    wcel
    #
    wtru
    1rp
    a1i
    vx
    cv
    #
    cc
    wcel
    #
    @0
    @8
    c1
    cD
    cbl
    cfv
    co
    #
    @0
    ccl
    cfv
    cfv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    wtru
    @9
    @13
    @11
    @0
    ccld
    cfv
    wcel
    #
    vy
    cv
    #
    cabs
    cfv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vy
    @11
    wral
    #
    vr
    cr
    wrex
    #
    @9
    @0
    ctop
    wcel
    #
    @10
    cc
    wss
    #
    @14
    @0
    @2
    cnfldtop
    #
    cD
    cc
    cxmt
    cfv
    wcel
    #
    @9
    c1
    cxr
    wcel
    #
    @22
    @5
    @24
    @6
    cD
    cc
    metxmet
    ax-mp
    #
    @7
    @25
    1rp
    c1
    rpxr
    ax-mp
    #
    cD
    @8
    c1
    cc
    blssm
    mp3an13
    #
    @10
    @0
    cc
    cc
    @0
    @0
    @2
    cnfldtopon
    toponunii
    #
    clscld
    sylancr
    @9
    @8
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @16
    @31
    cle
    wbr
    #
    vy
    @11
    wral
    #
    @20
    @9
    @30
    cr
    wcel
    #
    @32
    @8
    abscl
    #
    @30
    peano2re
    syl
    @9
    @11
    @33
    vy
    cab
    #
    wss
    @34
    @9
    @11
    @15
    cc
    wcel
    #
    @8
    @15
    cD
    co
    #
    c1
    cle
    wbr
    #
    wa
    #
    vy
    cab
    #
    @37
    @24
    @9
    @25
    @11
    @42
    wss
    @26
    @27
    vy
    cD
    @8
    c1
    @42
    @0
    cc
    @3
    @40
    vy
    cc
    crab
    @42
    @40
    vy
    cc
    df-rab
    eqcomi
    blcls
    mp3an13
    @9
    @41
    @33
    vy
    @9
    @41
    @33
    @9
    @41
    wa
    #
    @16
    @30
    cmin
    co
    #
    c1
    cle
    wbr
    @33
    @43
    @44
    @15
    @8
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    @43
    @16
    @30
    @38
    @16
    cr
    wcel
    @9
    @40
    @15
    abscl
    ad2antrl
    #
    @9
    @35
    @41
    @36
    adantr
    #
    resubcld
    @43
    @45
    @41
    @38
    @9
    @45
    cc
    wcel
    @9
    @38
    @40
    simpl
    @9
    id
    @15
    @8
    subcl
    syl2anr
    abscld
    @43
    1red
    #
    @43
    @15
    @8
    @9
    @38
    @40
    simprl
    @9
    @41
    simpl
    abs2difd
    @43
    @39
    @46
    c1
    cle
    @9
    @38
    @39
    @46
    wceq
    @40
    @9
    @38
    wa
    @39
    @8
    @15
    cmin
    co
    cabs
    cfv
    @46
    @8
    @15
    cD
    cncmet.1
    cnmetdval
    @8
    @15
    abssub
    eqtrd
    adantrr
    @9
    @38
    @40
    simprr
    eqbrtrrd
    letrd
    @43
    @16
    @30
    c1
    @47
    @48
    @49
    lesubadd2d
    mpbid
    ex
    ss2abdv
    sstrd
    @33
    vy
    @11
    ssabral
    sylib
    @19
    @34
    vr
    @31
    cr
    @17
    @31
    wceq
    @18
    @33
    vy
    @11
    @17
    @31
    @16
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    @9
    @11
    cc
    wss
    #
    @13
    @14
    @20
    wa
    wb
    @9
    @21
    @22
    @50
    @23
    @28
    @10
    @0
    cc
    @29
    clsss3
    sylancr
    vy
    @12
    @0
    @11
    vr
    @2
    @12
    eqid
    cnheibor
    syl
    mpbir2and
    adantl
    relcmpcmet
    trud
end
