include "cn.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "cwwlksn.mm"
include "c0.mm"
include "wne.mm"
include "ccatws1n0.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "simp2l.mm"
include "fstwrdne0.mm"
include "s1cld.mm"
include "3adant3.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "csn.mm"
include "wi.mm"
include "simprl.mm"
include "cn0.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "elfzonn0.mm"
include "adantl.mm"
include "nnz.mm"
include "elfzo0.mm"
include "cr.mm"
include "nn0re.mm"
include "nnre.mm"
include "peano2rem.mm"
include "syl.mm"
include "3jca.mm"
include "simpr.mm"
include "ltm1d.mm"
include "lttr.mm"
include "imp.mm"
include "syl12anc.mm"
include "ex.mm"
include "impancom.mm"
include "3adant2.mm"
include "sylbi.mm"
include "impcom.mm"
include "elfzo0z.mm"
include "syl3anbrc.mm"
include "adantlr.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "elfzom1p1elfzo.mm"
include "eleqtrrd.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "biimpcd.mm"
include "expdcom.mm"
include "3imp.mm"
include "fzo0end.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqcoms.mm"
include "lsw.mm"
include "eqtr4d.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "nncn.mm"
include "1cnd.mm"
include "npcand.mm"
include "ccatws1ls.mm"
include "3eqtr3rd.mm"
include "ovex.mm"
include "ralsn.mm"
include "sylibr.mm"
include "cun.mm"
include "addsubd.mm"
include "oveq2d.mm"
include "cuz.mm"
include "nnm1nn0.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"
include "raleqdv.mm"
include "ralunb.mm"
include "syl6bb.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"
include "ccatlen.mm"
include "id.mm"
include "s1len.mm"
include "a1i.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "cwwlks.mm"
include "nnnn0.mm"
include "iswwlksn.mm"
include "eqid.mm"
include "iswwlks.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "lswccats1.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "elrab2.mm"
include "sylanbrc.mm"

theorem clwwlkel
  let vw: setvar w
  let cD: class D
  let cP: class P
  let vi: setvar i
  let cG: class G
  let cN: class N
  assume clwwlkbij.d: |- D = { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) }

  disjoint G i
  disjoint G w
  disjoint N i
  disjoint N w
  disjoint P i
  disjoint P w
  assert |- ( ( N e. NN /\ ( P e. Word ( Vtx ` G ) /\ ( # ` P ) = N ) /\ ( A. i e. ( 0 ..^ ( N - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ( Edg ` G ) /\ { ( lastS ` P ) , ( P ` 0 ) } e. ( Edg ` G ) ) ) -> ( P ++ <" ( P ` 0 ) "> ) e. D )

  proof
    cN
    cn
    wcel
    #
    cP
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cP
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vi
    cv
    #
    cP
    cfv
    #
    @7
    c1
    caddc
    co
    #
    cP
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
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cP
    clsw
    cfv
    #
    cc0
    cP
    cfv
    #
    cpr
    #
    @12
    wcel
    #
    wa
    #
    w3a
    #
    cP
    @18
    cs1
    #
    cconcat
    co
    #
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    @24
    clsw
    cfv
    #
    cc0
    @24
    cfv
    #
    wceq
    #
    @24
    cD
    wcel
    @22
    @26
    @24
    c0
    wne
    #
    @24
    @2
    wcel
    #
    @7
    @24
    cfv
    #
    @9
    @24
    cfv
    #
    cpr
    #
    @12
    wcel
    #
    vi
    cc0
    @24
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
    w3a
    #
    @36
    cN
    c1
    caddc
    co
    #
    wceq
    #
    @22
    @30
    @31
    @39
    @6
    @0
    @30
    @21
    @3
    @30
    @5
    @1
    cP
    @18
    ccatws1n0
    adantr
    3ad2ant2
    @22
    @3
    @23
    @2
    wcel
    #
    @31
    @0
    @3
    @5
    @21
    simp2l
    @0
    @6
    @43
    @21
    @0
    @6
    wa
    #
    @18
    @1
    cN
    @1
    cP
    fstwrdne0
    #
    s1cld
    #
    3adant3
    @1
    cP
    @23
    ccatcl
    syl2anc
    @22
    @39
    @35
    vi
    cc0
    @41
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @22
    @49
    @35
    vi
    @15
    wral
    #
    @35
    vi
    @14
    csn
    #
    wral
    #
    @0
    @6
    @21
    @50
    @21
    @0
    @6
    @50
    @16
    @44
    @50
    wi
    @20
    @44
    @16
    @50
    @44
    @13
    @35
    vi
    @15
    @44
    @7
    @15
    wcel
    #
    wa
    #
    @11
    @34
    @12
    @54
    @8
    @32
    @10
    @33
    @54
    @32
    @8
    @54
    @3
    @43
    @7
    cc0
    @4
    cfzo
    co
    #
    wcel
    #
    @32
    @8
    wceq
    @44
    @3
    @53
    @0
    @3
    @5
    simprl
    #
    adantr
    #
    @44
    @43
    @53
    @46
    adantr
    #
    @54
    @56
    @7
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    @0
    @53
    @61
    @6
    @0
    @53
    wa
    @7
    cn0
    wcel
    #
    cN
    cz
    wcel
    #
    @7
    cN
    clt
    wbr
    #
    @61
    @53
    @62
    @0
    @7
    @14
    elfzonn0
    adantl
    @0
    @63
    @53
    cN
    nnz
    adantr
    @53
    @0
    @64
    @53
    @62
    @14
    cn
    wcel
    #
    @7
    @14
    clt
    wbr
    #
    w3a
    @0
    @64
    wi
    #
    @7
    @14
    elfzo0
    @62
    @66
    @67
    @65
    @62
    @0
    @66
    @64
    @62
    @0
    wa
    #
    @66
    @64
    @68
    @66
    wa
    @7
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    @66
    @14
    cN
    clt
    wbr
    #
    @64
    @68
    @72
    @66
    @68
    @69
    @70
    @71
    @62
    @69
    @0
    @7
    nn0re
    adantr
    @0
    @70
    @62
    @0
    @71
    @70
    cN
    nnre
    #
    cN
    peano2rem
    syl
    adantl
    @0
    @71
    @62
    @74
    adantl
    3jca
    adantr
    @68
    @66
    simpr
    @68
    @73
    @66
    @0
    @73
    @62
    @0
    cN
    @74
    ltm1d
    adantl
    adantr
    @72
    @66
    @73
    wa
    @64
    @7
    @14
    cN
    lttr
    imp
    syl12anc
    ex
    impancom
    3adant2
    sylbi
    impcom
    @7
    cN
    elfzo0z
    syl3anbrc
    adantlr
    @44
    @56
    @61
    wb
    #
    @53
    @5
    @75
    @0
    @3
    @5
    @55
    @60
    @7
    @4
    cN
    cc0
    cfzo
    oveq2
    #
    eleq2d
    ad2antll
    adantr
    mpbird
    @1
    cP
    @23
    @7
    ccatval1
    syl3anc
    eqcomd
    @54
    @33
    @10
    @54
    @3
    @43
    @9
    @55
    wcel
    @33
    @10
    wceq
    @58
    @59
    @54
    @9
    @60
    @55
    @0
    @53
    @9
    @60
    wcel
    @6
    cN
    @7
    elfzom1p1elfzo
    adantlr
    @44
    @55
    @60
    wceq
    #
    @53
    @5
    @77
    @0
    @3
    @76
    ad2antll
    adantr
    eleqtrrd
    @1
    cP
    @23
    @9
    ccatval1
    syl3anc
    eqcomd
    preq12d
    eleq1d
    ralbidva
    biimpcd
    adantr
    expdcom
    3imp
    @22
    @14
    @24
    cfv
    #
    @14
    c1
    caddc
    co
    #
    @24
    cfv
    #
    cpr
    #
    @12
    wcel
    #
    @52
    @0
    @6
    @21
    @82
    @21
    @0
    @6
    @82
    @20
    @44
    @82
    wi
    @16
    @44
    @20
    @82
    @44
    @19
    @81
    @12
    @44
    @17
    @78
    @18
    @80
    @44
    @78
    @14
    cP
    cfv
    #
    @17
    @44
    @3
    @43
    @14
    @55
    wcel
    #
    @78
    @83
    wceq
    @57
    @46
    @44
    @84
    @14
    @60
    wcel
    #
    @0
    @85
    @6
    cN
    fzo0end
    adantr
    @5
    @84
    @85
    wb
    @0
    @3
    @5
    @55
    @60
    @14
    @76
    eleq2d
    ad2antll
    mpbird
    @1
    cP
    @23
    @14
    ccatval1
    syl3anc
    @6
    @83
    @17
    wceq
    @0
    @6
    @83
    @4
    c1
    cmin
    co
    #
    cP
    cfv
    #
    @17
    @5
    @83
    @87
    wceq
    #
    @3
    @88
    cN
    @4
    cN
    @4
    wceq
    @14
    @86
    cP
    cN
    @4
    c1
    cmin
    oveq1
    fveq2d
    eqcoms
    adantl
    @3
    @17
    @87
    wceq
    @5
    cP
    @2
    lsw
    adantr
    eqtr4d
    adantl
    eqtr2d
    @44
    cN
    @24
    cfv
    #
    @4
    @24
    cfv
    #
    @80
    @18
    @5
    @89
    @90
    wceq
    #
    @0
    @3
    @91
    cN
    @4
    cN
    @4
    @24
    fveq2
    eqcoms
    ad2antll
    @0
    @89
    @80
    wceq
    @6
    @0
    cN
    @79
    @24
    @0
    @79
    cN
    @0
    cN
    c1
    cN
    nncn
    #
    @0
    1cnd
    #
    npcand
    eqcomd
    fveq2d
    adantr
    @44
    @3
    @18
    @1
    wcel
    #
    @90
    @18
    wceq
    @57
    @45
    @1
    cP
    @18
    ccatws1ls
    syl2anc
    3eqtr3rd
    preq12d
    eleq1d
    biimpcd
    adantl
    expdcom
    3imp
    @35
    @82
    vi
    @14
    cN
    c1
    cmin
    ovex
    @7
    @14
    wceq
    #
    @34
    @81
    @12
    @95
    @32
    @78
    @33
    @80
    @7
    @14
    @24
    fveq2
    @95
    @9
    @79
    @24
    @7
    @14
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    ralsn
    sylibr
    @0
    @6
    @49
    @50
    @52
    wa
    #
    wb
    @21
    @0
    @49
    @35
    vi
    @15
    @51
    cun
    #
    wral
    @96
    @0
    @35
    vi
    @48
    @97
    @0
    @48
    cc0
    @79
    cfzo
    co
    #
    @97
    @0
    @47
    @79
    cc0
    cfzo
    @0
    cN
    c1
    c1
    @92
    @93
    @93
    addsubd
    oveq2d
    @0
    @14
    cc0
    cuz
    cfv
    wcel
    #
    @98
    @97
    wceq
    @0
    @14
    cn0
    wcel
    @99
    cN
    nnm1nn0
    @14
    elnn0uz
    sylib
    cc0
    @14
    fzosplitsn
    syl
    eqtrd
    raleqdv
    @35
    vi
    @15
    @51
    ralunb
    syl6bb
    3ad2ant1
    mpbir2and
    @22
    @35
    vi
    @38
    @48
    @22
    @37
    @47
    cc0
    cfzo
    @22
    @36
    @41
    c1
    cmin
    @0
    @6
    @42
    @21
    @44
    @36
    @4
    @23
    chash
    cfv
    #
    caddc
    co
    #
    @41
    @44
    @3
    @43
    @36
    @101
    wceq
    @57
    @46
    @1
    cP
    @23
    ccatlen
    syl2anc
    @5
    @101
    @41
    wceq
    @0
    @3
    @5
    @4
    cN
    @100
    c1
    caddc
    @5
    id
    @100
    c1
    wceq
    @5
    @18
    s1len
    a1i
    oveq12d
    ad2antll
    eqtrd
    3adant3
    #
    oveq1d
    oveq2d
    raleqdv
    mpbird
    3jca
    @102
    @0
    @6
    @26
    @40
    @42
    wa
    #
    wb
    @21
    @0
    @26
    @24
    cG
    cwwlks
    cfv
    wcel
    #
    @42
    wa
    #
    @103
    @0
    cN
    cn0
    wcel
    @26
    @105
    wb
    cN
    nnnn0
    cG
    cN
    @24
    iswwlksn
    syl
    @0
    @104
    @40
    @42
    @104
    @40
    wb
    @0
    vi
    @12
    cG
    @1
    @24
    @1
    eqid
    @12
    eqid
    iswwlks
    a1i
    anbi1d
    bitrd
    3ad2ant1
    mpbir2and
    @0
    @6
    @29
    @21
    @44
    @27
    @18
    @28
    @44
    @3
    @94
    @27
    @18
    wceq
    @57
    @45
    @18
    @1
    cP
    lswccats1
    syl2anc
    @44
    @3
    @43
    cc0
    @55
    wcel
    #
    @28
    @18
    wceq
    @57
    @46
    @44
    @106
    cc0
    @60
    wcel
    #
    @0
    @107
    @6
    @107
    @0
    cN
    lbfzo0
    biimpri
    adantr
    @5
    @106
    @107
    wb
    @0
    @3
    @5
    @55
    @60
    cc0
    @76
    eleq2d
    ad2antll
    mpbird
    @1
    cP
    @23
    cc0
    ccatval1
    syl3anc
    eqtr4d
    3adant3
    vw
    cv
    #
    clsw
    cfv
    #
    cc0
    @108
    cfv
    #
    wceq
    @29
    vw
    @24
    @25
    cD
    @108
    @24
    wceq
    @109
    @27
    @110
    @28
    @108
    @24
    clsw
    fveq2
    cc0
    @108
    @24
    fveq1
    eqeq12d
    clwwlkbij.d
    elrab2
    sylanbrc
end
