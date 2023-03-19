include "c3.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "wo.mm"
include "cc0.mm"
include "cdioph.mm"
include "wn.mm"
include "pm4.42.mm"
include "ancom.mm"
include "wf.mm"
include "elmapi.mm"
include "df-2.mm"
include "df-3.mm"
include "ssid.mm"
include "jm2.27dlem5.mm"
include "1nn.mm"
include "jm2.27dlem3.mm"
include "sselii.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "adantr.mm"
include "elnn0.mm"
include "sylib.mm"
include "elnn1uz2.mm"
include "biimpi.mm"
include "orim1i.mm"
include "syl.mm"
include "biantrurd.mm"
include "andir.mm"
include "orbi1i.mm"
include "bitri.mm"
include "wb.mm"
include "cz.mm"
include "nnz.mm"
include "1exp.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "oveq1.mm"
include "bibi1d.mm"
include "syl5ibrcom.mm"
include "pm5.32d.mm"
include "iba.mm"
include "anbi1d.mm"
include "orbi12d.mm"
include "0exp.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "2nn.mm"
include "wi.mm"
include "pm2.53.mm"
include "sylbi.mm"
include "0nnn.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "impbid1.mm"
include "nn0cnd.mm"
include "exp0d.mm"
include "oveq2.mm"
include "rabbiia.mm"
include "cmpt.mm"
include "cmzp.mm"
include "3nn0.mm"
include "cvv.mm"
include "ovex.mm"
include "mzpproj.mm"
include "mp2an.mm"
include "elnnrabdioph.mm"
include "1z.mm"
include "mzpconstmpt.mm"
include "eqrabdioph.mm"
include "mp3an.mm"
include "3nn.mm"
include "anrabdioph.mm"
include "expdiophlem2.mm"
include "orrabdioph.mm"
include "eq0rabdioph.mm"
include "eqeltri.mm"

theorem expdioph
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e


  assert |- { a e. ( NN0 ^m ( 1 ... 3 ) ) | ( a ` 3 ) = ( ( a ` 1 ) ^ ( a ` 2 ) ) } e. ( Dioph ` 3 )

  proof
    c3
    va
    cv
    #
    cfv
    #
    c1
    @0
    cfv
    #
    c2
    @0
    cfv
    #
    cexp
    co
    #
    wceq
    #
    va
    cn0
    c1
    c3
    cfz
    co
    #
    cmap
    co
    #
    crab
    @3
    cn
    wcel
    #
    @2
    c1
    wceq
    #
    @1
    c1
    wceq
    #
    wa
    #
    @2
    c2
    cuz
    cfv
    wcel
    #
    @8
    wa
    #
    @5
    wa
    #
    wo
    #
    @2
    cc0
    wceq
    #
    @1
    cc0
    wceq
    #
    wa
    #
    wo
    #
    wa
    #
    @3
    cc0
    wceq
    #
    @10
    wa
    #
    wo
    #
    va
    @7
    crab
    #
    c3
    cdioph
    cfv
    #
    @5
    @23
    va
    @7
    @5
    @5
    @8
    wa
    #
    @5
    @8
    wn
    #
    wa
    #
    wo
    @0
    @7
    wcel
    #
    @23
    @5
    @8
    pm4.42
    @29
    @26
    @20
    @28
    @22
    @26
    @8
    @5
    wa
    @29
    @20
    @5
    @8
    ancom
    @29
    @8
    @5
    @19
    @29
    @8
    wa
    #
    @5
    @9
    @12
    wo
    #
    @16
    wo
    #
    @5
    wa
    #
    @19
    @30
    @32
    @5
    @30
    @2
    cn
    wcel
    #
    @16
    wo
    #
    @32
    @30
    @2
    cn0
    wcel
    #
    @35
    @29
    @36
    @8
    @29
    @6
    cn0
    @0
    wf
    #
    c1
    @6
    wcel
    #
    @36
    @0
    cn0
    @6
    elmapi
    #
    c1
    c1
    cfz
    co
    @6
    c1
    c1
    c2
    c3
    df-2
    c2
    c3
    c3
    df-3
    @6
    ssid
    jm2.27dlem5
    #
    jm2.27dlem5
    c1
    1nn
    jm2.27dlem3
    sselii
    #
    @6
    cn0
    c1
    @0
    ffvelrn
    sylancl
    #
    adantr
    @2
    elnn0
    sylib
    @34
    @31
    @16
    @34
    @31
    @2
    elnn1uz2
    biimpi
    orim1i
    syl
    biantrurd
    @33
    @9
    @5
    wa
    #
    @12
    @5
    wa
    #
    wo
    #
    @16
    @5
    wa
    #
    wo
    #
    @30
    @19
    @33
    @31
    @5
    wa
    #
    @46
    wo
    @47
    @31
    @16
    @5
    andir
    @48
    @45
    @46
    @9
    @12
    @5
    andir
    orbi1i
    bitri
    @30
    @45
    @15
    @46
    @18
    @30
    @43
    @11
    @44
    @14
    @30
    @9
    @5
    @10
    @30
    @5
    @10
    wb
    #
    @9
    @1
    c1
    @3
    cexp
    co
    #
    wceq
    #
    @10
    wb
    @30
    @50
    c1
    @1
    @8
    @50
    c1
    wceq
    #
    @29
    @8
    @3
    cz
    wcel
    @52
    @3
    nnz
    @3
    1exp
    syl
    adantl
    eqeq2d
    @9
    @5
    @51
    @10
    @9
    @4
    @50
    @1
    @2
    c1
    @3
    cexp
    oveq1
    eqeq2d
    bibi1d
    syl5ibrcom
    pm5.32d
    @30
    @12
    @13
    @5
    @8
    @12
    @13
    wb
    @29
    @8
    @12
    iba
    adantl
    anbi1d
    orbi12d
    @30
    @16
    @5
    @17
    @30
    @5
    @17
    wb
    @16
    @1
    cc0
    @3
    cexp
    co
    #
    wceq
    #
    @17
    wb
    @30
    @53
    cc0
    @1
    @8
    @53
    cc0
    wceq
    @29
    @3
    0exp
    adantl
    eqeq2d
    @16
    @5
    @54
    @17
    @16
    @4
    @53
    @1
    @2
    cc0
    @3
    cexp
    oveq1
    eqeq2d
    bibi1d
    syl5ibrcom
    pm5.32d
    orbi12d
    syl5bb
    bitrd
    pm5.32da
    syl5bb
    @28
    @27
    @5
    wa
    #
    @29
    @22
    @5
    @27
    ancom
    @29
    @55
    @21
    @5
    wa
    @22
    @29
    @27
    @21
    @5
    @29
    @3
    cn0
    wcel
    #
    @27
    @21
    wb
    @29
    @37
    c2
    @6
    wcel
    #
    @56
    @39
    c1
    c2
    cfz
    co
    @6
    c2
    @40
    c2
    2nn
    jm2.27dlem3
    sselii
    #
    @6
    cn0
    c2
    @0
    ffvelrn
    sylancl
    @56
    @27
    @21
    @56
    @8
    @21
    wo
    @27
    @21
    wi
    @3
    elnn0
    @8
    @21
    pm2.53
    sylbi
    @21
    @8
    cc0
    cn
    wcel
    0nnn
    @3
    cc0
    cn
    eleq1
    mtbiri
    impbid1
    syl
    anbi1d
    @29
    @21
    @5
    @10
    @29
    @49
    @21
    @1
    @2
    cc0
    cexp
    co
    #
    wceq
    #
    @10
    wb
    @29
    @59
    c1
    @1
    @29
    @2
    @29
    @2
    @42
    nn0cnd
    exp0d
    eqeq2d
    @21
    @5
    @60
    @10
    @21
    @4
    @59
    @1
    @3
    cc0
    @2
    cexp
    oveq2
    eqeq2d
    bibi1d
    syl5ibrcom
    pm5.32d
    bitrd
    syl5bb
    orbi12d
    syl5bb
    rabbiia
    @20
    va
    @7
    crab
    @25
    wcel
    #
    @22
    va
    @7
    crab
    @25
    wcel
    #
    @24
    @25
    wcel
    @8
    va
    @7
    crab
    @25
    wcel
    #
    @19
    va
    @7
    crab
    @25
    wcel
    #
    @61
    c3
    cn0
    wcel
    #
    va
    cz
    @6
    cmap
    co
    #
    @3
    cmpt
    @6
    cmzp
    cfv
    #
    wcel
    #
    @63
    3nn0
    @6
    cvv
    wcel
    #
    @57
    @68
    c1
    c3
    cfz
    ovex
    #
    @58
    va
    @6
    c2
    mzpproj
    mp2an
    #
    va
    @3
    c3
    elnnrabdioph
    mp2an
    @15
    va
    @7
    crab
    @25
    wcel
    #
    @18
    va
    @7
    crab
    @25
    wcel
    #
    @64
    @11
    va
    @7
    crab
    @25
    wcel
    #
    @14
    va
    @7
    crab
    @25
    wcel
    @72
    @9
    va
    @7
    crab
    @25
    wcel
    #
    @10
    va
    @7
    crab
    @25
    wcel
    #
    @74
    @65
    va
    @66
    @2
    cmpt
    @67
    wcel
    #
    va
    @66
    c1
    cmpt
    @67
    wcel
    #
    @75
    3nn0
    @69
    @38
    @77
    @70
    @41
    va
    @6
    c1
    mzpproj
    mp2an
    #
    @69
    c1
    cz
    wcel
    @78
    @70
    1z
    va
    c1
    @6
    mzpconstmpt
    mp2an
    #
    va
    @2
    c1
    c3
    eqrabdioph
    mp3an
    @65
    va
    @66
    @1
    cmpt
    @67
    wcel
    #
    @78
    @76
    3nn0
    @69
    c3
    @6
    wcel
    @81
    @70
    c3
    3nn
    jm2.27dlem3
    va
    @6
    c3
    mzpproj
    mp2an
    #
    @80
    va
    @1
    c1
    c3
    eqrabdioph
    mp3an
    #
    @9
    @10
    va
    c3
    anrabdioph
    mp2an
    va
    expdiophlem2
    @11
    @14
    va
    c3
    orrabdioph
    mp2an
    @16
    va
    @7
    crab
    @25
    wcel
    #
    @17
    va
    @7
    crab
    @25
    wcel
    #
    @73
    @65
    @77
    @84
    3nn0
    @79
    va
    @2
    c3
    eq0rabdioph
    mp2an
    @65
    @81
    @85
    3nn0
    @82
    va
    @1
    c3
    eq0rabdioph
    mp2an
    @16
    @17
    va
    c3
    anrabdioph
    mp2an
    @15
    @18
    va
    c3
    orrabdioph
    mp2an
    @8
    @19
    va
    c3
    anrabdioph
    mp2an
    @21
    va
    @7
    crab
    @25
    wcel
    #
    @76
    @62
    @65
    @68
    @86
    3nn0
    @71
    va
    @3
    c3
    eq0rabdioph
    mp2an
    @83
    @21
    @10
    va
    c3
    anrabdioph
    mp2an
    @20
    @22
    va
    c3
    orrabdioph
    mp2an
    eqeltri
end
