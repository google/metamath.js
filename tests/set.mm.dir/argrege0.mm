include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "clog.mm"
include "cim.mm"
include "cr.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cicc.mm"
include "logcl.mm"
include "3adant3.mm"
include "imcld.mm"
include "cabs.mm"
include "wa.mm"
include "ccos.mm"
include "ci.mm"
include "cmul.mm"
include "ce.mm"
include "simp3.mm"
include "simp1.mm"
include "abscld.mm"
include "recnd.mm"
include "mul01d.mm"
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
include "lemul2d.mm"
include "mpbird.mm"
include "wceq.mm"
include "efiarg.mm"
include "breqtrrd.mm"
include "recosval.mm"
include "syl.mm"
include "clt.mm"
include "wn.mm"
include "wb.mm"
include "halfpire.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpge0.mm"
include "mp2b.mm"
include "pire.mm"
include "rphalflt.mm"
include "ax-mp.mm"
include "ltleii.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "absge0d.mm"
include "logimcl.mm"
include "simpld.mm"
include "wi.mm"
include "renegcli.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "simprd.mm"
include "absle.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "syl3anbrc.mm"
include "cosord.mm"
include "fveq2.mm"
include "cosneg.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "absord.mm"
include "mpjaod.mm"
include "coshalfpi.mm"
include "breq12d.mm"
include "bitrd.mm"
include "notbid.mm"
include "lenlt.mm"
include "recoscld.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem argrege0
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 /\ 0 <_ ( Re ` A ) ) -> ( Im ` ( log ` A ) ) e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cc0
    cA
    cre
    cfv
    #
    cle
    wbr
    #
    w3a
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
    @6
    cle
    wbr
    #
    @6
    @8
    cle
    wbr
    #
    @6
    @9
    @8
    cicc
    co
    wcel
    @4
    @5
    @0
    @1
    @5
    cc
    wcel
    @3
    cA
    logcl
    3adant3
    imcld
    #
    @4
    @10
    @11
    @4
    @6
    cabs
    cfv
    #
    @8
    cle
    wbr
    #
    @10
    @11
    wa
    #
    @4
    @14
    cc0
    @6
    ccos
    cfv
    #
    cle
    wbr
    #
    @4
    cc0
    ci
    @6
    cmul
    co
    ce
    cfv
    #
    cre
    cfv
    #
    @16
    cle
    @4
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
    @19
    cle
    @4
    cc0
    @22
    cle
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
    cle
    wbr
    @4
    cc0
    @2
    @23
    @24
    cle
    @0
    @1
    @3
    simp3
    @4
    @20
    @4
    @20
    @4
    cA
    @0
    @1
    @3
    simp1
    #
    abscld
    #
    recnd
    #
    mul01d
    @4
    @20
    @21
    cmul
    co
    #
    cre
    cfv
    @24
    @2
    @4
    @20
    @21
    @26
    @4
    cA
    @20
    @25
    @27
    @4
    @20
    @0
    @1
    @20
    crp
    wcel
    @3
    cA
    absrpcl
    3adant3
    #
    rpne0d
    #
    divcld
    #
    remul2d
    @4
    @28
    cA
    cre
    @4
    cA
    @20
    @25
    @27
    @30
    divcan2d
    fveq2d
    eqtr3d
    3brtr4d
    @4
    cc0
    @22
    @20
    cc0
    cr
    wcel
    #
    @4
    0re
    a1i
    @4
    @21
    @31
    recld
    @29
    lemul2d
    mpbird
    @4
    @18
    @21
    cre
    @0
    @1
    @18
    @21
    wceq
    @3
    cA
    efiarg
    3adant3
    fveq2d
    breqtrrd
    @4
    @7
    @16
    @19
    wceq
    @12
    @6
    recosval
    syl
    breqtrrd
    @4
    @8
    @13
    clt
    wbr
    #
    wn
    #
    @16
    cc0
    clt
    wbr
    #
    wn
    #
    @14
    @17
    @4
    @33
    @35
    @4
    @33
    @13
    ccos
    cfv
    #
    @8
    ccos
    cfv
    #
    clt
    wbr
    #
    @35
    @4
    @8
    cc0
    cpi
    cicc
    co
    #
    wcel
    #
    @13
    @40
    wcel
    #
    @33
    @39
    wb
    @41
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    @8
    cpi
    cle
    wbr
    halfpire
    cpi
    crp
    wcel
    #
    @8
    crp
    wcel
    @44
    pirp
    cpi
    rphalfcl
    @8
    rpge0
    mp2b
    @8
    cpi
    halfpire
    pire
    @45
    @8
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
    @8
    0re
    pire
    elicc2i
    mpbir3an
    @4
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    @13
    cpi
    cle
    wbr
    #
    @42
    @4
    @6
    @4
    @6
    @12
    recnd
    #
    abscld
    #
    @4
    @6
    @48
    absge0d
    @4
    @47
    cpi
    cneg
    #
    @6
    cle
    wbr
    #
    @6
    cpi
    cle
    wbr
    #
    @4
    @50
    @6
    clt
    wbr
    #
    @51
    @4
    @53
    @52
    @0
    @1
    @53
    @52
    wa
    @3
    cA
    logimcl
    3adant3
    #
    simpld
    @4
    @50
    cr
    wcel
    @7
    @53
    @51
    wi
    cpi
    pire
    renegcli
    @12
    @50
    @6
    ltle
    sylancr
    mpd
    @4
    @53
    @52
    @54
    simprd
    @4
    @7
    cpi
    cr
    wcel
    @47
    @51
    @52
    wa
    wb
    @12
    pire
    @6
    cpi
    absle
    sylancl
    mpbir2and
    cc0
    cpi
    @13
    0re
    pire
    elicc2i
    syl3anbrc
    @8
    @13
    cosord
    sylancr
    @4
    @37
    @16
    @38
    cc0
    clt
    @4
    @13
    @6
    wceq
    #
    @37
    @16
    wceq
    #
    @13
    @6
    cneg
    #
    wceq
    #
    @55
    @56
    wi
    @4
    @13
    @6
    ccos
    fveq2
    a1i
    @4
    @56
    @58
    @57
    ccos
    cfv
    #
    @16
    wceq
    #
    @4
    @6
    cc
    wcel
    @60
    @48
    @6
    cosneg
    syl
    @58
    @37
    @59
    @16
    @13
    @57
    ccos
    fveq2
    eqeq1d
    syl5ibrcom
    @4
    @6
    @12
    absord
    mpjaod
    @38
    cc0
    wceq
    @4
    coshalfpi
    a1i
    breq12d
    bitrd
    notbid
    @4
    @46
    @43
    @14
    @34
    wb
    @49
    halfpire
    @13
    @8
    lenlt
    sylancl
    @4
    @32
    @16
    cr
    wcel
    @17
    @36
    wb
    0re
    @4
    @6
    @12
    recoscld
    cc0
    @16
    lenlt
    sylancr
    3bitr4d
    mpbird
    @4
    @7
    @43
    @14
    @15
    wb
    @12
    halfpire
    @6
    @8
    absle
    sylancl
    mpbid
    #
    simpld
    @4
    @10
    @11
    @61
    simprd
    @9
    @8
    @6
    @8
    halfpire
    renegcli
    halfpire
    elicc2i
    syl3anbrc
end
