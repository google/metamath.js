include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cbits.mm"
include "cfv.mm"
include "cdif.mm"
include "cneg.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "wn.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "bitsval2.mm"
include "wb.mm"
include "2z.mm"
include "a1i.mm"
include "simpl.mm"
include "zred.mm"
include "cn.mm"
include "2nn.mm"
include "simpr.mm"
include "nnexpcld.mm"
include "nndivred.mm"
include "flcld.mm"
include "dvdsnegb.mm"
include "syl2anc.mm"
include "notbid.mm"
include "znegcld.mm"
include "oddm1even.mm"
include "syl.mm"
include "wceq.mm"
include "cle.mm"
include "caddc.mm"
include "clt.mm"
include "cmul.mm"
include "cr.mm"
include "flltp1.mm"
include "1red.mm"
include "readdcld.mm"
include "ltnegd.mm"
include "mpbid.mm"
include "recnd.mm"
include "negdi2d.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divnegd.mm"
include "3brtr3d.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "renegcld.mm"
include "nnrpd.mm"
include "ltmuldivd.mm"
include "mpbird.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "zltlem1.mm"
include "resubcld.mm"
include "lemuldivd.mm"
include "flle.mm"
include "lenegd.mm"
include "eqbrtrrd.mm"
include "ledivmuld.mm"
include "zlem1lt.mm"
include "ltdivmuld.mm"
include "negcld.mm"
include "npcand.mm"
include "breqtrrd.mm"
include "flbi.mm"
include "mpbir2and.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "3bitrd.mm"
include "pm5.32da.mm"
include "znegcl.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "eldif.mm"
include "w3a.mm"
include "bitsval.mm"
include "3anass.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem bitscmp
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let cM: class M
  let vn: setvar n


  assert |- ( N e. ZZ -> ( NN0 \ ( bits ` N ) ) = ( bits ` ( -u N - 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    vm
    cn0
    cN
    cbits
    cfv
    #
    cdif
    #
    cN
    cneg
    #
    c1
    cmin
    co
    #
    cbits
    cfv
    #
    @0
    vm
    cv
    #
    cn0
    wcel
    #
    @6
    @1
    wcel
    #
    wn
    #
    wa
    #
    @4
    cz
    wcel
    #
    @7
    c2
    @4
    c2
    @6
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    @6
    @2
    wcel
    @6
    @5
    wcel
    #
    @0
    @10
    @17
    @18
    @0
    @7
    @9
    @16
    @0
    @7
    wa
    #
    @8
    @15
    @20
    @8
    c2
    cN
    @12
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    c2
    @22
    cneg
    #
    cdvds
    wbr
    #
    wn
    #
    @15
    @6
    cN
    bitsval2
    @20
    @23
    @25
    @20
    c2
    cz
    wcel
    #
    @22
    cz
    wcel
    @23
    @25
    wb
    @27
    @20
    2z
    a1i
    @20
    @21
    @20
    cN
    @12
    @20
    cN
    @0
    @7
    simpl
    #
    zred
    #
    @20
    c2
    @6
    c2
    cn
    wcel
    @20
    2nn
    a1i
    @0
    @7
    simpr
    nnexpcld
    #
    nndivred
    #
    flcld
    #
    c2
    @22
    dvdsnegb
    syl2anc
    notbid
    @20
    @26
    c2
    @24
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    @15
    @20
    @24
    cz
    wcel
    @26
    @34
    wb
    @20
    @22
    @32
    znegcld
    #
    @24
    oddm1even
    syl
    @20
    @14
    @33
    c2
    cdvds
    @20
    @14
    @33
    wceq
    #
    @33
    @13
    cle
    wbr
    #
    @13
    @33
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @20
    @33
    @12
    cmul
    co
    #
    @4
    cle
    wbr
    #
    @37
    @20
    @40
    @3
    clt
    wbr
    #
    @41
    @20
    @42
    @33
    @3
    @12
    cdiv
    co
    #
    clt
    wbr
    @20
    @22
    c1
    caddc
    co
    #
    cneg
    #
    @21
    cneg
    #
    @33
    @43
    clt
    @20
    @21
    @44
    clt
    wbr
    #
    @45
    @46
    clt
    wbr
    @20
    @21
    cr
    wcel
    #
    @47
    @31
    @21
    flltp1
    syl
    @20
    @21
    @44
    @31
    @20
    @22
    c1
    @20
    @22
    @32
    zred
    #
    @20
    1red
    #
    readdcld
    ltnegd
    mpbid
    @20
    @22
    c1
    @20
    @22
    @49
    recnd
    #
    @20
    c1
    @50
    recnd
    #
    negdi2d
    @20
    cN
    @12
    @20
    cN
    @29
    recnd
    @20
    @12
    @30
    nncnd
    @20
    @12
    @30
    nnne0d
    divnegd
    #
    3brtr3d
    @20
    @33
    @3
    @12
    @20
    @33
    @20
    @24
    c1
    @35
    @20
    1zzd
    zsubcld
    #
    zred
    #
    @20
    cN
    @29
    renegcld
    #
    @20
    @12
    @30
    nnrpd
    #
    ltmuldivd
    mpbird
    @20
    @40
    cz
    wcel
    @3
    cz
    wcel
    #
    @42
    @41
    wb
    @20
    @33
    @12
    @54
    @20
    @12
    @30
    nnzd
    #
    zmulcld
    @20
    cN
    @28
    znegcld
    #
    @40
    @3
    zltlem1
    syl2anc
    mpbid
    @20
    @33
    @4
    @12
    @55
    @20
    @3
    c1
    @56
    @50
    resubcld
    #
    @57
    lemuldivd
    mpbid
    @20
    @13
    @24
    @38
    clt
    @20
    @13
    @24
    clt
    wbr
    @4
    @12
    @24
    cmul
    co
    #
    clt
    wbr
    #
    @20
    @3
    @62
    cle
    wbr
    #
    @63
    @20
    @43
    @24
    cle
    wbr
    @64
    @20
    @46
    @43
    @24
    cle
    @53
    @20
    @22
    @21
    cle
    wbr
    #
    @46
    @24
    cle
    wbr
    @20
    @48
    @65
    @31
    @21
    flle
    syl
    @20
    @22
    @21
    @49
    @31
    lenegd
    mpbid
    eqbrtrrd
    @20
    @3
    @24
    @12
    @56
    @20
    @22
    @49
    renegcld
    #
    @57
    ledivmuld
    mpbid
    @20
    @58
    @62
    cz
    wcel
    @64
    @63
    wb
    @60
    @20
    @12
    @24
    @59
    @35
    zmulcld
    @3
    @62
    zlem1lt
    syl2anc
    mpbid
    @20
    @4
    @24
    @12
    @61
    @66
    @57
    ltdivmuld
    mpbird
    @20
    @24
    c1
    @20
    @22
    @51
    negcld
    @52
    npcand
    breqtrrd
    @20
    @13
    cr
    wcel
    @33
    cz
    wcel
    @36
    @37
    @39
    wa
    wb
    @20
    @4
    @12
    @61
    @30
    nndivred
    @54
    @13
    @33
    flbi
    syl2anc
    mpbir2and
    breq2d
    bitr4d
    3bitrd
    notbid
    pm5.32da
    @0
    @11
    @17
    @0
    @3
    c1
    cN
    znegcl
    @0
    1zzd
    zsubcld
    biantrurd
    bitrd
    @6
    cn0
    @1
    eldif
    @19
    @11
    @7
    @16
    w3a
    @18
    @6
    @4
    bitsval
    @11
    @7
    @16
    3anass
    bitri
    3bitr4g
    eqrdv
end
