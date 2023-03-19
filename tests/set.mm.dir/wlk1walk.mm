include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cin.mm"
include "chash.mm"
include "cle.mm"
include "cfzo.mm"
include "wral.mm"
include "wlkv.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "cfz.mm"
include "cvtx.mm"
include "wf.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "eqid.mm"
include "iswlk.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "fvex.mm"
include "inex1.mm"
include "wi.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "wkslem1.mm"
include "rspcv.mm"
include "syl.mm"
include "imp.mm"
include "elfzofz.mm"
include "fz1fzo0m1.mm"
include "3syl.mm"
include "wn.mm"
include "wo.mm"
include "df-ifp.mm"
include "cz.mm"
include "cc.mm"
include "wb.mm"
include "elfzoelz.mm"
include "zcn.mm"
include "eqidd.mm"
include "npcan1.mm"
include "wkslem2.mm"
include "syl2anc.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "snid.mm"
include "fveq1i.mm"
include "eleq2i.mm"
include "eleq2.mm"
include "syl5bb.mm"
include "mpbiri.mm"
include "syl6eleqr.mm"
include "anim12i.mm"
include "ex.mm"
include "syl6bi.mm"
include "com12.mm"
include "adantl.mm"
include "prss.mm"
include "eqcomi.mm"
include "biimpi.mm"
include "adantr.mm"
include "sylbir.mm"
include "jaoi.mm"
include "anbi12i.mm"
include "sylbi.mm"
include "com3r.mm"
include "mp2d.mm"
include "ancoms.mm"
include "inelcm.mm"
include "hashge1.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "3ad2ant3.mm"
include "mpcom.mm"

theorem wlk1walk
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let vi: setvar i
  assume wlk1walk.i: |- I = ( iEdg ` G )

  disjoint F k
  disjoint G k
  disjoint P k
  disjoint F i
  disjoint i k
  disjoint G i
  disjoint P i
  assert |- ( F ( Walks ` G ) P -> A. k e. ( 1 ..^ ( # ` F ) ) 1 <_ ( # ` ( ( I ` ( F ` ( k - 1 ) ) ) i^i ( I ` ( F ` k ) ) ) ) )

  proof
    cG
    cvv
    wcel
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    w3a
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    c1
    vk
    cv
    #
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @2
    cF
    cfv
    #
    cI
    cfv
    #
    cin
    #
    chash
    cfv
    cle
    wbr
    #
    vk
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    cP
    cF
    cG
    wlkv
    @0
    @1
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    @10
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    vi
    cv
    #
    cP
    cfv
    #
    @17
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @17
    cF
    cfv
    @13
    cfv
    #
    @18
    csn
    wceq
    @18
    @19
    cpr
    @20
    wss
    wif
    #
    vi
    cc0
    @10
    cfzo
    co
    #
    wral
    #
    w3a
    @12
    cP
    cvv
    vi
    cF
    cG
    @13
    @15
    cvv
    cvv
    @15
    eqid
    @13
    eqid
    iswlk
    @23
    @14
    @12
    @16
    @23
    @9
    vk
    @11
    @23
    @2
    @11
    wcel
    #
    wa
    #
    @8
    cvv
    wcel
    @8
    c0
    wne
    #
    @9
    @5
    @7
    @4
    cI
    fvex
    inex1
    @25
    @2
    cP
    cfv
    #
    @5
    wcel
    #
    @27
    @7
    wcel
    #
    wa
    #
    @26
    @24
    @23
    @30
    @24
    @23
    wa
    @27
    @2
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @6
    @13
    cfv
    #
    @27
    csn
    #
    wceq
    #
    @27
    @32
    cpr
    @34
    wss
    #
    wif
    #
    @3
    cP
    cfv
    #
    @3
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    @4
    @13
    cfv
    #
    @39
    csn
    #
    wceq
    #
    @39
    @41
    cpr
    @42
    wss
    wif
    #
    @30
    @24
    @23
    @38
    @24
    @2
    @22
    wcel
    @23
    @38
    wi
    @11
    @22
    @2
    @10
    fzo0ss1
    sseli
    @21
    @38
    vi
    @2
    @22
    @17
    @2
    cP
    cF
    @13
    wkslem1
    rspcv
    syl
    imp
    @24
    @23
    @45
    @24
    @2
    c1
    @10
    cfz
    co
    wcel
    @3
    @22
    wcel
    @23
    @45
    wi
    @2
    c1
    @10
    elfzofz
    @2
    @10
    fz1fzo0m1
    @21
    @45
    vi
    @3
    @22
    @17
    @3
    cP
    cF
    @13
    wkslem1
    rspcv
    3syl
    imp
    @24
    @38
    @45
    @30
    wi
    #
    wi
    @23
    @38
    @24
    @46
    @38
    @33
    @36
    wa
    #
    @33
    wn
    #
    @37
    wa
    #
    wo
    #
    @24
    @46
    wi
    @33
    @36
    @37
    df-ifp
    @24
    @45
    @50
    @30
    @24
    @45
    @39
    @27
    wceq
    #
    @44
    @39
    @27
    cpr
    @42
    wss
    #
    wif
    #
    @50
    @30
    wi
    #
    @24
    @2
    cz
    wcel
    @2
    cc
    wcel
    #
    @45
    @53
    wb
    #
    @2
    c1
    @10
    elfzoelz
    @2
    zcn
    @55
    @3
    @3
    wceq
    @40
    @2
    wceq
    @56
    @55
    @3
    eqidd
    @2
    npcan1
    @3
    @3
    @2
    cP
    cF
    @13
    wkslem2
    syl2anc
    3syl
    @53
    @51
    @44
    wa
    #
    @51
    wn
    #
    @52
    wa
    #
    wo
    @54
    @51
    @44
    @52
    df-ifp
    @57
    @54
    @59
    @50
    @57
    @30
    @47
    @57
    @30
    wi
    #
    @49
    @36
    @60
    @33
    @57
    @36
    @30
    @51
    @44
    @36
    @30
    wi
    #
    @51
    @44
    @42
    @35
    wceq
    #
    @61
    @51
    @43
    @35
    @42
    @39
    @27
    sneq
    eqeq2d
    #
    @62
    @36
    @30
    @62
    @28
    @36
    @29
    @62
    @28
    @27
    @35
    wcel
    #
    @27
    @2
    cP
    fvex
    #
    snid
    #
    @28
    @27
    @42
    wcel
    #
    @62
    @64
    @5
    @42
    @27
    @4
    cI
    @13
    wlk1walk.i
    fveq1i
    eleq2i
    @42
    @35
    @27
    eleq2
    syl5bb
    mpbiri
    #
    @36
    @27
    @34
    @7
    @36
    @27
    @34
    wcel
    #
    @64
    @66
    @34
    @35
    @27
    eleq2
    #
    mpbiri
    @6
    cI
    @13
    wlk1walk.i
    fveq1i
    #
    syl6eleqr
    anim12i
    ex
    syl6bi
    imp
    com12
    adantl
    @37
    @60
    @48
    @57
    @37
    @30
    @51
    @44
    @37
    @30
    wi
    #
    @51
    @44
    @62
    @72
    @63
    @62
    @37
    @30
    @62
    @28
    @37
    @29
    @68
    @37
    @69
    @32
    @34
    wcel
    #
    wa
    #
    @29
    @27
    @32
    @34
    @65
    @31
    cP
    fvex
    prss
    #
    @69
    @29
    @73
    @69
    @29
    @34
    @7
    @27
    @6
    @13
    cI
    cI
    @13
    wlk1walk.i
    eqcomi
    #
    fveq1i
    eleq2i
    #
    biimpi
    adantr
    sylbir
    anim12i
    ex
    syl6bi
    imp
    com12
    adantl
    jaoi
    com12
    @50
    @59
    @30
    @47
    @59
    @30
    wi
    #
    @49
    @36
    @78
    @33
    @59
    @36
    @30
    @52
    @61
    @58
    @52
    @39
    @42
    wcel
    #
    @67
    wa
    #
    @61
    @39
    @27
    @42
    @3
    cP
    fvex
    @65
    prss
    #
    @67
    @61
    @79
    @67
    @36
    @30
    @67
    @28
    @36
    @29
    @67
    @28
    @42
    @5
    @27
    @4
    @13
    cI
    @76
    fveq1i
    eleq2i
    #
    biimpi
    @36
    @29
    @64
    @66
    @29
    @69
    @36
    @64
    @7
    @34
    @27
    @71
    eleq2i
    @70
    syl5bb
    mpbiri
    anim12i
    ex
    adantl
    sylbir
    adantl
    com12
    adantl
    @37
    @78
    @48
    @37
    @74
    @78
    @75
    @69
    @78
    @73
    @59
    @69
    @30
    @52
    @69
    @30
    wi
    #
    @58
    @52
    @80
    @83
    @81
    @67
    @83
    @79
    @67
    @69
    @30
    @67
    @69
    wa
    @30
    @67
    @28
    @69
    @29
    @82
    @77
    anbi12i
    biimpi
    ex
    adantl
    sylbir
    adantl
    com12
    adantr
    sylbir
    adantl
    jaoi
    com12
    jaoi
    sylbi
    syl6bi
    com3r
    sylbi
    com12
    adantr
    mp2d
    ancoms
    @27
    @5
    @7
    inelcm
    syl
    @8
    cvv
    hashge1
    sylancr
    ralrimiva
    3ad2ant3
    syl6bi
    mpcom
end
