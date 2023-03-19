include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "clog.mm"
include "cim.mm"
include "cr.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wne.mm"
include "recl.mm"
include "gt0ne0.mm"
include "sylan.mm"
include "wceq.mm"
include "fveq2.mm"
include "re0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "logcl.mm"
include "syldan.mm"
include "imcld.mm"
include "cabs.mm"
include "ccos.mm"
include "coshalfpi.mm"
include "ci.mm"
include "cmul.mm"
include "ce.mm"
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
include "remul2d.mm"
include "divcan2d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "3brtr4d.mm"
include "0re.mm"
include "a1i.mm"
include "recld.mm"
include "ltmul2d.mm"
include "mpbird.mm"
include "efiarg.mm"
include "breqtrrd.mm"
include "recosval.mm"
include "wi.mm"
include "cosneg.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "absord.mm"
include "mpjaod.mm"
include "syl5eqbr.mm"
include "cicc.mm"
include "wb.mm"
include "cle.mm"
include "absge0d.mm"
include "logimcl.mm"
include "simpld.mm"
include "pire.mm"
include "renegcli.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "simprd.mm"
include "absle.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "halfpire.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpge0.mm"
include "mp2b.mm"
include "rphalflt.mm"
include "ax-mp.mm"
include "ltleii.mm"
include "mpbir3an.mm"
include "cosord.mm"
include "abslt.mm"
include "mpbid.mm"
include "cxr.mm"
include "w3a.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"

theorem argregt0
  let cA: class A


  assert |- ( ( A e. CC /\ 0 < ( Re ` A ) ) -> ( Im ` ( log ` A ) ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cc0
    cA
    cre
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
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @5
    clt
    wbr
    #
    @5
    @7
    clt
    wbr
    #
    @5
    @8
    @7
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
    @12
    @0
    @1
    cr
    wcel
    @2
    @13
    cA
    recl
    @1
    gt0ne0
    sylan
    cA
    cc0
    @1
    cc0
    cA
    cc0
    wceq
    @1
    cc0
    cre
    cfv
    cc0
    cA
    cc0
    cre
    fveq2
    re0
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
    @9
    @10
    @3
    @5
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @9
    @10
    wa
    #
    @3
    @17
    @7
    ccos
    cfv
    #
    @16
    ccos
    cfv
    #
    clt
    wbr
    #
    @3
    @19
    cc0
    @20
    clt
    coshalfpi
    @3
    cc0
    @5
    ccos
    cfv
    #
    @20
    clt
    @3
    cc0
    ci
    @5
    cmul
    co
    ce
    cfv
    #
    cre
    cfv
    #
    @22
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
    cre
    cfv
    #
    @24
    clt
    @3
    cc0
    @27
    clt
    wbr
    @25
    cc0
    cmul
    co
    #
    @25
    @27
    cmul
    co
    #
    clt
    wbr
    @3
    cc0
    @1
    @28
    @29
    clt
    @0
    @2
    simpr
    @3
    @25
    @3
    @25
    @0
    @25
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
    @25
    @26
    cmul
    co
    #
    cre
    cfv
    @29
    @1
    @3
    @25
    @26
    @30
    @3
    cA
    @25
    @0
    @2
    simpl
    #
    @31
    @3
    @25
    @0
    @2
    @12
    @25
    crp
    wcel
    @14
    cA
    absrpcl
    syldan
    #
    rpne0d
    #
    divcld
    #
    remul2d
    @3
    @32
    cA
    cre
    @3
    cA
    @25
    @33
    @31
    @35
    divcan2d
    fveq2d
    eqtr3d
    3brtr4d
    @3
    cc0
    @27
    @25
    cc0
    cr
    wcel
    @3
    0re
    a1i
    @3
    @26
    @36
    recld
    @34
    ltmul2d
    mpbird
    @3
    @23
    @26
    cre
    @0
    @2
    @12
    @23
    @26
    wceq
    @14
    cA
    efiarg
    syldan
    fveq2d
    breqtrrd
    @3
    @6
    @22
    @24
    wceq
    @15
    @5
    recosval
    syl
    breqtrrd
    @3
    @16
    @5
    wceq
    #
    @20
    @22
    wceq
    #
    @16
    @5
    cneg
    #
    wceq
    #
    @37
    @38
    wi
    @3
    @16
    @5
    ccos
    fveq2
    a1i
    @3
    @38
    @40
    @39
    ccos
    cfv
    #
    @22
    wceq
    #
    @3
    @5
    cc
    wcel
    #
    @42
    @3
    @5
    @15
    recnd
    #
    @5
    cosneg
    syl
    @40
    @20
    @41
    @22
    @16
    @39
    ccos
    fveq2
    eqeq1d
    syl5ibrcom
    @3
    @5
    @15
    absord
    mpjaod
    breqtrrd
    syl5eqbr
    @3
    @16
    cc0
    cpi
    cicc
    co
    #
    wcel
    #
    @7
    @45
    wcel
    #
    @17
    @21
    wb
    @3
    @16
    cr
    wcel
    #
    cc0
    @16
    cle
    wbr
    @16
    cpi
    cle
    wbr
    #
    @46
    @3
    @43
    @48
    @44
    @5
    abscl
    syl
    @3
    @5
    @44
    absge0d
    @3
    @49
    cpi
    cneg
    #
    @5
    cle
    wbr
    #
    @5
    cpi
    cle
    wbr
    #
    @3
    @50
    @5
    clt
    wbr
    #
    @51
    @3
    @53
    @52
    @0
    @2
    @12
    @53
    @52
    wa
    @14
    cA
    logimcl
    syldan
    #
    simpld
    @3
    @50
    cr
    wcel
    @6
    @53
    @51
    wi
    cpi
    pire
    renegcli
    @15
    @50
    @5
    ltle
    sylancr
    mpd
    @3
    @53
    @52
    @54
    simprd
    @3
    @6
    cpi
    cr
    wcel
    @49
    @51
    @52
    wa
    wb
    @15
    pire
    @5
    cpi
    absle
    sylancl
    mpbir2and
    cc0
    cpi
    @16
    0re
    pire
    elicc2i
    syl3anbrc
    @47
    @7
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    cpi
    cle
    wbr
    halfpire
    cpi
    crp
    wcel
    #
    @7
    crp
    wcel
    @56
    pirp
    cpi
    rphalfcl
    @7
    rpge0
    mp2b
    @7
    cpi
    halfpire
    pire
    @57
    @7
    cpi
    clt
    wbr
    pirp
    cpi
    rphalflt
    ax-mp
    ltleii
    cc0
    cpi
    @7
    0re
    pire
    elicc2i
    mpbir3an
    @16
    @7
    cosord
    sylancl
    mpbird
    @3
    @6
    @55
    @17
    @18
    wb
    @15
    halfpire
    @5
    @7
    abslt
    sylancl
    mpbid
    #
    simpld
    @3
    @9
    @10
    @58
    simprd
    @8
    cxr
    wcel
    @7
    cxr
    wcel
    @11
    @6
    @9
    @10
    w3a
    wb
    @8
    @7
    halfpire
    renegcli
    rexri
    @7
    halfpire
    rexri
    @8
    @7
    @5
    elioo2
    mp2an
    syl3anbrc
end
