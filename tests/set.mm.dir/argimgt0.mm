include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cim.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "clog.mm"
include "cr.mm"
include "cpi.mm"
include "cioo.mm"
include "co.mm"
include "wne.mm"
include "imcl.mm"
include "gt0ne0.mm"
include "sylan.mm"
include "wceq.mm"
include "fveq2.mm"
include "im0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "logcl.mm"
include "syldan.mm"
include "imcld.mm"
include "csin.mm"
include "cneg.mm"
include "ci.mm"
include "cmul.mm"
include "ce.mm"
include "cabs.mm"
include "cdiv.mm"
include "simpr.mm"
include "abscl.mm"
include "adantr.mm"
include "recnd.mm"
include "mul01d.mm"
include "simpl.mm"
include "crp.mm"
include "absrpcl.mm"
include "rpne0d.mm"
include "divcld.mm"
include "immul2d.mm"
include "divcan2d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "3brtr4d.mm"
include "0re.mm"
include "a1i.mm"
include "ltmul2d.mm"
include "mpbird.mm"
include "efiarg.mm"
include "breqtrrd.mm"
include "resinval.mm"
include "resincld.mm"
include "lt0neg2d.mm"
include "mpbid.mm"
include "cle.mm"
include "wn.mm"
include "caddc.mm"
include "cicc.mm"
include "pire.mm"
include "readdcl.mm"
include "sylancl.mm"
include "cmin.mm"
include "df-neg.mm"
include "logimcl.mm"
include "simpld.mm"
include "wi.mm"
include "renegcli.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "syl5eqbrr.mm"
include "lesubaddd.mm"
include "leadd1d.mm"
include "biimpa.mm"
include "picn.mm"
include "addid2i.mm"
include "syl6breq.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "sinq12ge0.mm"
include "sinppi.mm"
include "breqtrd.mm"
include "ex.mm"
include "con3d.mm"
include "wb.mm"
include "renegcld.mm"
include "ltnle.mm"
include "3imtr4d.mm"
include "rpre.mm"
include "negneg.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "lognegb.mm"
include "reim0b.mm"
include "3imtr3d.mm"
include "necon3d.mm"
include "necomd.mm"
include "simprd.mm"
include "leltned.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"

theorem argimgt0
  let cA: class A


  assert |- ( ( A e. CC /\ 0 < ( Im ` A ) ) -> ( Im ` ( log ` A ) ) e. ( 0 (,) _pi ) )

  proof
    cA
    cc
    wcel
    #
    cc0
    cA
    cim
    cfv
    #
    clt
    wbr
    #
    wa
    #
    cA
    clog
    cfv
    #
    cim
    cfv
    #
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @5
    cpi
    clt
    wbr
    #
    @5
    cc0
    cpi
    cioo
    co
    wcel
    #
    @3
    @4
    @0
    @2
    cA
    cc0
    wne
    #
    @4
    cc
    wcel
    @3
    @1
    cc0
    wne
    #
    @10
    @0
    @1
    cr
    wcel
    @2
    @11
    cA
    imcl
    @1
    gt0ne0
    sylan
    #
    cA
    cc0
    @1
    cc0
    cA
    cc0
    wceq
    @1
    cc0
    cim
    cfv
    cc0
    cA
    cc0
    cim
    fveq2
    im0
    syl6eq
    necon3i
    syl
    #
    cA
    logcl
    syldan
    imcld
    #
    @3
    @5
    csin
    cfv
    #
    cneg
    #
    cc0
    clt
    wbr
    #
    @7
    @3
    cc0
    @15
    clt
    wbr
    @17
    @3
    cc0
    ci
    @5
    cmul
    co
    ce
    cfv
    #
    cim
    cfv
    #
    @15
    clt
    @3
    cc0
    cA
    cA
    cabs
    cfv
    #
    cdiv
    co
    #
    cim
    cfv
    #
    @19
    clt
    @3
    cc0
    @22
    clt
    wbr
    @20
    cc0
    cmul
    co
    #
    @20
    @22
    cmul
    co
    #
    clt
    wbr
    @3
    cc0
    @1
    @23
    @24
    clt
    @0
    @2
    simpr
    @3
    @20
    @3
    @20
    @0
    @20
    cr
    wcel
    @2
    cA
    abscl
    adantr
    #
    recnd
    #
    mul01d
    @3
    @20
    @21
    cmul
    co
    #
    cim
    cfv
    @24
    @1
    @3
    @20
    @21
    @25
    @3
    cA
    @20
    @0
    @2
    simpl
    #
    @26
    @3
    @20
    @0
    @2
    @10
    @20
    crp
    wcel
    @13
    cA
    absrpcl
    syldan
    #
    rpne0d
    #
    divcld
    #
    immul2d
    @3
    @27
    cA
    cim
    @3
    cA
    @20
    @28
    @26
    @30
    divcan2d
    fveq2d
    eqtr3d
    3brtr4d
    @3
    cc0
    @22
    @20
    cc0
    cr
    wcel
    #
    @3
    0re
    a1i
    #
    @3
    @21
    @31
    imcld
    @29
    ltmul2d
    mpbird
    @3
    @18
    @21
    cim
    @0
    @2
    @10
    @18
    @21
    wceq
    @13
    cA
    efiarg
    syldan
    fveq2d
    breqtrrd
    @3
    @6
    @15
    @19
    wceq
    @14
    @5
    resinval
    syl
    breqtrrd
    @3
    @15
    @3
    @5
    @14
    resincld
    #
    lt0neg2d
    mpbid
    @3
    cc0
    @16
    cle
    wbr
    #
    wn
    #
    @5
    cc0
    cle
    wbr
    #
    wn
    #
    @17
    @7
    @3
    @37
    @35
    @3
    @37
    @35
    @3
    @37
    wa
    #
    cc0
    @5
    cpi
    caddc
    co
    #
    csin
    cfv
    #
    @16
    cle
    @39
    @40
    cc0
    cpi
    cicc
    co
    wcel
    #
    cc0
    @41
    cle
    wbr
    @39
    @40
    cr
    wcel
    #
    cc0
    @40
    cle
    wbr
    #
    @40
    cpi
    cle
    wbr
    @42
    @3
    @43
    @37
    @3
    @6
    cpi
    cr
    wcel
    #
    @43
    @14
    pire
    @5
    cpi
    readdcl
    sylancl
    adantr
    @3
    @44
    @37
    @3
    cc0
    cpi
    cmin
    co
    #
    @5
    cle
    wbr
    @44
    @3
    @46
    cpi
    cneg
    #
    @5
    cle
    cpi
    df-neg
    @3
    @47
    @5
    clt
    wbr
    #
    @47
    @5
    cle
    wbr
    #
    @3
    @48
    @5
    cpi
    cle
    wbr
    #
    @0
    @2
    @10
    @48
    @50
    wa
    @13
    cA
    logimcl
    syldan
    #
    simpld
    @3
    @47
    cr
    wcel
    @6
    @48
    @49
    wi
    cpi
    pire
    renegcli
    @14
    @47
    @5
    ltle
    sylancr
    mpd
    syl5eqbrr
    @3
    cc0
    cpi
    @5
    @33
    @45
    @3
    pire
    a1i
    #
    @14
    lesubaddd
    mpbid
    adantr
    @39
    @40
    cc0
    cpi
    caddc
    co
    #
    cpi
    cle
    @3
    @37
    @40
    @53
    cle
    wbr
    @3
    @5
    cc0
    cpi
    @14
    @33
    @52
    leadd1d
    biimpa
    cpi
    picn
    addid2i
    syl6breq
    cc0
    cpi
    @40
    0re
    pire
    elicc2i
    syl3anbrc
    @40
    sinq12ge0
    syl
    @3
    @41
    @16
    wceq
    #
    @37
    @3
    @5
    cc
    wcel
    @54
    @3
    @5
    @14
    recnd
    @5
    sinppi
    syl
    adantr
    breqtrd
    ex
    con3d
    @3
    @16
    cr
    wcel
    @32
    @17
    @36
    wb
    @3
    @15
    @34
    renegcld
    0re
    @16
    cc0
    ltnle
    sylancl
    @3
    @32
    @6
    @7
    @38
    wb
    0re
    @14
    cc0
    @5
    ltnle
    sylancr
    3imtr4d
    mpd
    @3
    @8
    cpi
    @5
    wne
    @3
    @5
    cpi
    @3
    @11
    @5
    cpi
    wne
    @12
    @3
    @5
    cpi
    @1
    cc0
    @3
    cA
    cneg
    #
    crp
    wcel
    #
    cA
    cr
    wcel
    #
    @5
    cpi
    wceq
    #
    @1
    cc0
    wceq
    #
    @56
    @55
    cneg
    #
    cr
    wcel
    @3
    @57
    @56
    @55
    @55
    rpre
    renegcld
    @3
    @60
    cA
    cr
    @0
    @60
    cA
    wceq
    @2
    cA
    negneg
    adantr
    eleq1d
    syl5ib
    @0
    @2
    @10
    @56
    @58
    wb
    @13
    cA
    lognegb
    syldan
    @0
    @57
    @59
    wb
    @2
    cA
    reim0b
    adantr
    3imtr3d
    necon3d
    mpd
    necomd
    @3
    @5
    cpi
    @14
    @52
    @3
    @48
    @50
    @51
    simprd
    leltned
    mpbird
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @9
    @6
    @7
    @8
    w3a
    wb
    0xr
    cpi
    pire
    rexri
    cc0
    cpi
    @5
    elioo2
    mp2an
    syl3anbrc
end
