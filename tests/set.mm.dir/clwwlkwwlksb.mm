include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "cwwlks.mm"
include "cclwwlk.mm"
include "csn.mm"
include "wceq.mm"
include "simpl.mm"
include "fstwrdne.mm"
include "s1cld.mm"
include "jca.mm"
include "ccatlen.mm"
include "syl.mm"
include "s1len.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "1cnd.mm"
include "addsubd.mm"
include "raleqdv.mm"
include "cun.mm"
include "cuz.mm"
include "cn0.mm"
include "cn.mm"
include "lennncl.mm"
include "nnm1nn0.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzosplitsn.mm"
include "wb.mm"
include "ralunb.mm"
include "bitrd.mm"
include "cz.mm"
include "nn0zd.mm"
include "elfzom1elfzo.mm"
include "sylan.mm"
include "ccats1val1.mm"
include "syl3anc.mm"
include "elfzom1elp1fzo.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "ovex.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ralsn.mm"
include "fzo0end.mm"
include "lsw.mm"
include "eqcomd.mm"
include "npcan1.mm"
include "eqidd.mm"
include "ccats1val2.mm"
include "anbi12d.mm"
include "ccat0.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "adantld.mm"
include "mpcom.mm"
include "cvv.mm"
include "wrdv.mm"
include "s1cli.mm"
include "ccatalpha.mm"
include "mpbird.mm"
include "w3a.mm"
include "eqid.mm"
include "iswwlks.mm"
include "df-3an.mm"
include "bitri.mm"
include "mpbirand.mm"
include "isclwwlk.mm"
include "3anass.mm"
include "baib.mm"
include "3bitr4rd.mm"

theorem clwwlkwwlksb
  let cG: class G
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume clwwlkwwlksb.v: |- V = ( Vtx ` G )


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( W e. ( ClWWalks ` G ) <-> ( W ++ <" ( W ` 0 ) "> ) e. ( WWalks ` G ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    c0
    wne
    #
    wa
    #
    vi
    cv
    #
    cW
    cc0
    cW
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cfv
    #
    @4
    c1
    caddc
    co
    #
    @7
    cfv
    #
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
    @7
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
    @4
    cW
    cfv
    #
    @9
    cW
    cfv
    #
    cpr
    #
    @12
    wcel
    #
    vi
    cc0
    cW
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
    cW
    clsw
    cfv
    #
    @5
    cpr
    #
    @12
    wcel
    #
    wa
    #
    @7
    cG
    cwwlks
    cfv
    wcel
    #
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    @3
    @17
    @13
    vi
    @24
    wral
    #
    @13
    vi
    @23
    csn
    #
    wral
    #
    wa
    #
    @29
    @3
    @17
    @13
    vi
    cc0
    @23
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wral
    #
    @35
    @3
    @13
    vi
    @16
    @37
    @3
    @15
    @36
    cc0
    cfzo
    @3
    @15
    @22
    c1
    caddc
    co
    #
    c1
    cmin
    co
    @36
    @3
    @14
    @39
    c1
    cmin
    @3
    @14
    @22
    @6
    chash
    cfv
    #
    caddc
    co
    #
    @39
    @3
    @1
    @6
    @0
    wcel
    #
    wa
    #
    @14
    @41
    wceq
    @3
    @1
    @42
    @1
    @2
    simpl
    #
    @3
    @5
    cV
    cV
    cW
    fstwrdne
    #
    s1cld
    jca
    #
    cV
    cW
    @6
    ccatlen
    syl
    @3
    @40
    c1
    @22
    caddc
    @40
    c1
    wceq
    @3
    @5
    s1len
    a1i
    oveq2d
    eqtrd
    oveq1d
    @3
    @22
    c1
    c1
    @1
    @22
    cc
    wcel
    #
    @2
    @1
    @22
    cV
    cW
    lencl
    #
    nn0cnd
    #
    adantr
    @3
    1cnd
    #
    @50
    addsubd
    eqtrd
    oveq2d
    raleqdv
    @3
    @38
    @13
    vi
    @24
    @33
    cun
    #
    wral
    #
    @35
    @3
    @13
    vi
    @37
    @51
    @3
    @23
    cc0
    cuz
    cfv
    wcel
    #
    @37
    @51
    wceq
    @3
    @23
    cn0
    wcel
    #
    @53
    @3
    @22
    cn
    wcel
    #
    @54
    cV
    cW
    lennncl
    #
    @22
    nnm1nn0
    syl
    @23
    elnn0uz
    sylib
    cc0
    @23
    fzosplitsn
    syl
    raleqdv
    @52
    @35
    wb
    @3
    @13
    vi
    @24
    @33
    ralunb
    a1i
    bitrd
    bitrd
    @3
    @32
    @25
    @34
    @28
    @3
    @13
    @21
    vi
    @24
    @3
    @4
    @24
    wcel
    #
    wa
    #
    @11
    @20
    @12
    @58
    @8
    @18
    @10
    @19
    @58
    @1
    @5
    cV
    wcel
    #
    @4
    cc0
    @22
    cfzo
    co
    #
    wcel
    #
    @8
    @18
    wceq
    @3
    @1
    @57
    @44
    adantr
    #
    @3
    @59
    @57
    @45
    adantr
    #
    @3
    @22
    cz
    wcel
    #
    @57
    @61
    @1
    @64
    @2
    @1
    @22
    @48
    nn0zd
    adantr
    #
    @4
    @22
    elfzom1elfzo
    sylan
    @5
    @4
    cV
    cW
    ccats1val1
    syl3anc
    @58
    @1
    @59
    @9
    @60
    wcel
    #
    @10
    @19
    wceq
    @62
    @63
    @3
    @64
    @57
    @66
    @65
    @4
    @22
    elfzom1elp1fzo
    sylan
    @5
    @9
    cV
    cW
    ccats1val1
    syl3anc
    preq12d
    eleq1d
    ralbidva
    @3
    @34
    @23
    @7
    cfv
    #
    @36
    @7
    cfv
    #
    cpr
    #
    @12
    wcel
    #
    @28
    @34
    @70
    wb
    @3
    @13
    @70
    vi
    @23
    @22
    c1
    cmin
    ovex
    @4
    @23
    wceq
    #
    @11
    @69
    @12
    @71
    @8
    @67
    @10
    @68
    @4
    @23
    @7
    fveq2
    @71
    @9
    @36
    @7
    @4
    @23
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    ralsn
    a1i
    @3
    @69
    @27
    @12
    @3
    @67
    @26
    @68
    @5
    @3
    @67
    @23
    cW
    cfv
    #
    @26
    @3
    @1
    @59
    @23
    @60
    wcel
    #
    @67
    @72
    wceq
    @44
    @45
    @3
    @55
    @73
    @56
    @22
    fzo0end
    syl
    @5
    @23
    cV
    cW
    ccats1val1
    syl3anc
    @1
    @72
    @26
    wceq
    @2
    @1
    @26
    @72
    cW
    @0
    lsw
    eqcomd
    adantr
    eqtrd
    @3
    @68
    @22
    @7
    cfv
    #
    @5
    @3
    @36
    @22
    @7
    @1
    @36
    @22
    wceq
    #
    @2
    @1
    @47
    @75
    @49
    @22
    npcan1
    syl
    adantr
    fveq2d
    @3
    @1
    @59
    @22
    @22
    wceq
    @74
    @5
    wceq
    @44
    @45
    @3
    @22
    eqidd
    @5
    @22
    cV
    cW
    ccats1val2
    syl3anc
    eqtrd
    preq12d
    eleq1d
    bitrd
    anbi12d
    bitrd
    @3
    @30
    @7
    c0
    wne
    #
    @7
    @0
    wcel
    #
    wa
    #
    @17
    @3
    @76
    @77
    @43
    @3
    @76
    @46
    @43
    @2
    @76
    @1
    @43
    @7
    c0
    cW
    c0
    @43
    @7
    c0
    wceq
    cW
    c0
    wceq
    #
    @6
    c0
    wceq
    #
    wa
    @79
    cV
    cW
    @6
    ccat0
    @79
    @80
    simpl
    syl6bi
    necon3d
    adantld
    mpcom
    @3
    @77
    @43
    @46
    @3
    cW
    cvv
    cword
    #
    wcel
    #
    @6
    @81
    wcel
    #
    wa
    #
    @77
    @43
    wb
    @1
    @84
    @2
    @1
    @82
    @83
    cV
    cW
    wrdv
    @83
    @1
    @5
    s1cli
    a1i
    jca
    adantr
    cW
    @6
    cV
    ccatalpha
    syl
    mpbird
    jca
    @30
    @78
    @17
    wa
    #
    wb
    @3
    @30
    @76
    @77
    @17
    w3a
    @85
    vi
    @12
    cG
    cV
    @7
    clwwlkwwlksb.v
    @12
    eqid
    #
    iswwlks
    @76
    @77
    @17
    df-3an
    bitri
    a1i
    mpbirand
    @31
    @3
    @29
    @31
    @3
    @25
    @28
    w3a
    @3
    @29
    wa
    vi
    @12
    cG
    cV
    cW
    clwwlkwwlksb.v
    @86
    isclwwlk
    @3
    @25
    @28
    3anass
    bitri
    baib
    3bitr4rd
end
