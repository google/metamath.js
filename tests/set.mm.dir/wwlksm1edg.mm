include "cwwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "c0.mm"
include "wne.mm"
include "cvtx.mm"
include "cword.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "iswwlks.mm"
include "wa.mm"
include "cin.mm"
include "cn0.mm"
include "lencl.mm"
include "cn.mm"
include "simpl.mm"
include "1red.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nn0re.mm"
include "adantr.mm"
include "1le2.mm"
include "simpr.mm"
include "letrd.mm"
include "jca.mm"
include "elnnnn0c.mm"
include "sylibr.mm"
include "lbfzo0.mm"
include "nn0ge2m1nn.mm"
include "sylan.mm"
include "inelcm.mm"
include "syl.mm"
include "wceq.mm"
include "cres.mm"
include "wfn.mm"
include "wb.mm"
include "wrdfn.mm"
include "fnresdisj.mm"
include "cfz.mm"
include "nn0ge2m1nn0.mm"
include "lem1d.mm"
include "3jca.mm"
include "elfz2nn0.mm"
include "swrd0val.mm"
include "eqeq1d.mm"
include "bicomd.mm"
include "syldan.mm"
include "bitr2d.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "3ad2antl2.mm"
include "swrdcl.mm"
include "a1d.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "wss.mm"
include "cuz.mm"
include "cz.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "peano2rem.mm"
include "eluz2.mm"
include "swrd0len.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "fzoss2.mm"
include "ssralv.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "fzossrbm1.mm"
include "sselda.mm"
include "swrd0fv.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "elfzom1p1elfzo.mm"
include "preq12d.mm"
include "ex.mm"
include "sylbid.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "syld.mm"
include "expcom.mm"
include "com3l.mm"
include "3imp1.mm"
include "syl3anbrc.mm"
include "sylbi.mm"

theorem wwlksm1edg
  let cG: class G
  let cW: class W
  let vx: setvar x


  assert |- ( ( W e. ( WWalks ` G ) /\ 2 <_ ( # ` W ) ) -> ( W substr <. 0 , ( ( # ` W ) - 1 ) >. ) e. ( WWalks ` G ) )

  proof
    cW
    cG
    cwwlks
    cfv
    #
    wcel
    #
    c2
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    cW
    cc0
    @2
    c1
    cmin
    co
    #
    cop
    csubstr
    co
    #
    @0
    wcel
    #
    @1
    cW
    c0
    wne
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    vx
    cv
    #
    cW
    cfv
    #
    @11
    c1
    caddc
    co
    #
    cW
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
    vx
    cc0
    @4
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @3
    @6
    wi
    vx
    @16
    cG
    @8
    cW
    @8
    eqid
    #
    @16
    eqid
    #
    iswwlks
    @20
    @3
    @6
    @20
    @3
    wa
    @5
    c0
    wne
    #
    @5
    @9
    wcel
    #
    @11
    @5
    cfv
    #
    @13
    @5
    cfv
    #
    cpr
    #
    @16
    wcel
    #
    vx
    cc0
    @5
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
    @6
    @10
    @7
    @3
    @23
    @19
    @10
    @3
    wa
    #
    @23
    cc0
    @2
    cfzo
    co
    #
    @18
    cin
    #
    c0
    wne
    #
    @33
    cc0
    @34
    wcel
    #
    cc0
    @18
    wcel
    #
    wa
    #
    @36
    @10
    @2
    cn0
    wcel
    #
    @3
    @39
    @8
    cW
    lencl
    #
    @40
    @3
    wa
    #
    @37
    @38
    @42
    @2
    cn
    wcel
    #
    @37
    @42
    @40
    c1
    @2
    cle
    wbr
    #
    wa
    @43
    @42
    @40
    @44
    @40
    @3
    simpl
    #
    @42
    c1
    c2
    @2
    @42
    1red
    c2
    cr
    wcel
    @42
    2re
    a1i
    @40
    @2
    cr
    wcel
    #
    @3
    @2
    nn0re
    #
    adantr
    #
    c1
    c2
    cle
    wbr
    @42
    1le2
    a1i
    @40
    @3
    simpr
    letrd
    jca
    @2
    elnnnn0c
    sylibr
    @2
    lbfzo0
    sylibr
    @42
    @4
    cn
    wcel
    #
    @38
    @2
    nn0ge2m1nn
    #
    @4
    lbfzo0
    sylibr
    jca
    sylan
    cc0
    @34
    @18
    inelcm
    syl
    @33
    @5
    c0
    @35
    c0
    @33
    @35
    c0
    wceq
    #
    cW
    @18
    cres
    #
    c0
    wceq
    #
    @5
    c0
    wceq
    #
    @33
    cW
    @34
    wfn
    #
    @51
    @53
    wb
    @10
    @55
    @3
    @8
    cW
    wrdfn
    adantr
    @34
    @18
    cW
    fnresdisj
    syl
    @10
    @3
    @4
    cc0
    @2
    cfz
    co
    wcel
    #
    @53
    @54
    wb
    @33
    @4
    cn0
    wcel
    #
    @40
    @4
    @2
    cle
    wbr
    #
    w3a
    #
    @56
    @10
    @40
    @3
    @59
    @41
    @42
    @57
    @40
    @58
    @2
    nn0ge2m1nn0
    #
    @45
    @42
    @2
    @48
    lem1d
    3jca
    sylan
    @4
    @2
    elfz2nn0
    #
    sylibr
    #
    @10
    @56
    wa
    #
    @54
    @53
    @63
    @5
    @52
    c0
    @8
    cW
    @4
    swrd0val
    eqeq1d
    bicomd
    syldan
    bitr2d
    necon3bid
    mpbird
    3ad2antl2
    @20
    @3
    @24
    @10
    @7
    @3
    @24
    wi
    @19
    @10
    @24
    @3
    @8
    cW
    cc0
    @4
    swrdcl
    a1d
    3ad2ant2
    imp
    @7
    @10
    @19
    @3
    @32
    @10
    @19
    @3
    @32
    wi
    wi
    wi
    @7
    @3
    @10
    @19
    @32
    @10
    @3
    @19
    @32
    wi
    @33
    @19
    @17
    vx
    @31
    wral
    #
    @32
    @33
    @31
    @18
    wss
    #
    @19
    @64
    wi
    @33
    @4
    @30
    cuz
    cfv
    #
    wcel
    @65
    @33
    @4
    @4
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    @66
    @33
    @67
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @67
    @4
    cle
    wbr
    #
    w3a
    #
    @4
    @68
    wcel
    @10
    @40
    @3
    @72
    @41
    @42
    @69
    @70
    @71
    @40
    @69
    @3
    @40
    @70
    @69
    @40
    @2
    cz
    wcel
    @70
    @2
    nn0z
    @2
    peano2zm
    syl
    #
    @4
    peano2zm
    syl
    adantr
    @40
    @70
    @3
    @73
    adantr
    @40
    @71
    @3
    @40
    @4
    @40
    @46
    @4
    cr
    wcel
    @47
    @2
    peano2rem
    syl
    lem1d
    adantr
    3jca
    sylan
    @67
    @4
    eluz2
    sylibr
    @33
    @30
    @67
    cuz
    @10
    @3
    @56
    @30
    @67
    wceq
    @33
    @59
    @56
    @10
    @40
    @3
    @59
    @41
    @42
    @57
    @40
    @58
    @60
    @45
    @40
    @58
    @3
    @40
    @2
    @47
    lem1d
    adantr
    3jca
    sylan
    @61
    sylibr
    #
    @63
    @29
    @4
    c1
    cmin
    @8
    cW
    @4
    swrd0len
    #
    oveq1d
    syldan
    fveq2d
    eleqtrrd
    @30
    cc0
    @4
    fzoss2
    syl
    @17
    vx
    @31
    @18
    ssralv
    syl
    @33
    @17
    @28
    vx
    @31
    @33
    @11
    @31
    wcel
    #
    wa
    #
    @17
    @28
    @77
    @15
    @27
    @16
    @33
    @76
    @15
    @27
    wceq
    #
    @33
    @76
    @11
    cc0
    @67
    cfzo
    co
    #
    wcel
    #
    @78
    @33
    @31
    @79
    @11
    @33
    @30
    @67
    cc0
    cfzo
    @33
    @29
    @4
    c1
    cmin
    @10
    @3
    @56
    @29
    @4
    wceq
    @74
    @75
    syldan
    oveq1d
    oveq2d
    eleq2d
    @33
    @80
    @78
    @33
    @80
    wa
    #
    @12
    @25
    @14
    @26
    @81
    @25
    @12
    @81
    @10
    @56
    @11
    @18
    wcel
    @25
    @12
    wceq
    @33
    @10
    @80
    @10
    @3
    simpl
    adantr
    #
    @33
    @56
    @80
    @62
    adantr
    #
    @33
    @79
    @18
    @11
    @33
    @57
    @79
    @18
    wss
    #
    @10
    @40
    @3
    @57
    @41
    @60
    sylan
    @57
    @70
    @84
    @4
    nn0z
    @4
    fzossrbm1
    syl
    syl
    sselda
    @11
    @4
    @8
    cW
    swrd0fv
    syl3anc
    eqcomd
    @81
    @26
    @14
    @81
    @10
    @56
    @13
    @18
    wcel
    #
    @26
    @14
    wceq
    @82
    @83
    @33
    @49
    @80
    @85
    @10
    @40
    @3
    @49
    @41
    @50
    sylan
    @4
    @11
    elfzom1p1elfzo
    sylan
    @13
    @4
    @8
    cW
    swrd0fv
    syl3anc
    eqcomd
    preq12d
    ex
    sylbid
    imp
    eleq1d
    biimpd
    ralimdva
    syld
    expcom
    com3l
    a1i
    3imp1
    vx
    @16
    cG
    @8
    @5
    @21
    @22
    iswwlks
    syl3anbrc
    ex
    sylbi
    imp
end
