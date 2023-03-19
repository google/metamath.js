include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cn.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "ovex.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cr.mm"
include "cle.mm"
include "wss.mm"
include "elpwi.mm"
include "cuz.mm"
include "nnuz.mm"
include "sumeq1i.mm"
include "1nn.mm"
include "rpnnen2lem6.mm"
include "mpan2.mm"
include "syl5eqel.mm"
include "syl.mm"
include "1zzd.mm"
include "wa.mm"
include "eqidd.mm"
include "wf.mm"
include "rpnnen2lem2.mm"
include "ffvelrnda.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "rpnnen2lem5.mm"
include "sylancl.mm"
include "ssid.mm"
include "rpnnen2lem4.mm"
include "mp3an2.mm"
include "simpld.mm"
include "sylan.mm"
include "isumge0.mm"
include "c2.mm"
include "cdiv.mm"
include "halfre.mm"
include "a1i.mm"
include "1re.mm"
include "rpnnen2lem7.mm"
include "mp3an23.mm"
include "eqid.mm"
include "cc.mm"
include "elnnuz.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "recnd.mm"
include "sylbir.mm"
include "adantl.mm"
include "rpnnen2lem3.mm"
include "isumclim.mm"
include "breqtrd.mm"
include "syl5eqbr.mm"
include "halflt1.mm"
include "ltleii.mm"
include "letrd.mm"
include "0re.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "wceq.mm"
include "wne.mm"
include "clt.mm"
include "wb.mm"
include "wi.mm"
include "wral.mm"
include "cdif.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "cun.mm"
include "c0.mm"
include "ssdifss.mm"
include "unss.mm"
include "biimpi.mm"
include "syl2an.mm"
include "eqss.mm"
include "ssdif0.mm"
include "anbi12i.mm"
include "un00.mm"
include "3bitri.mm"
include "necon3bii.mm"
include "nnwo.mm"
include "ex.mm"
include "sselda.mm"
include "wal.mm"
include "df-ral.mm"
include "con34b.mm"
include "eldif.mm"
include "orbi12i.mm"
include "elun.mm"
include "xor.mm"
include "3bitr4ri.mm"
include "con1bii.mm"
include "imbi2i.mm"
include "bitri.mm"
include "albii.mm"
include "alral.mm"
include "nnre.mm"
include "ltnle.mm"
include "syl2anr.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "syl5ibr.mm"
include "syl5bi.mm"
include "reximdva.mm"
include "syld.mm"
include "rexun.mm"
include "syl6ib.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "biid.mm"
include "rpnnen2lem11.mm"
include "rexlimdvaa.mm"
include "bicom.mm"
include "ralbii.mm"
include "sylibr.mm"
include "eqcom.mm"
include "jaod.mm"
include "necon4ad.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sumeq2sdv.mm"
include "impbid1.mm"
include "dom2.mm"

theorem rpnnen2lem12
  let vx: setvar x
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint N n
  assert |- ~P NN ~<_ ( 0 [,] 1 )

  proof
    cc0
    c1
    cicc
    co
    #
    cvv
    wcel
    cn
    cpw
    #
    @0
    cdom
    wbr
    cc0
    c1
    cicc
    ovex
    vy
    vz
    @1
    @0
    cn
    vk
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vk
    csu
    #
    cn
    @2
    vz
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vk
    csu
    #
    cvv
    @3
    @1
    wcel
    #
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    @6
    c1
    cle
    wbr
    @6
    @0
    wcel
    @11
    @3
    cn
    wss
    #
    @12
    @3
    cn
    elpwi
    #
    @13
    @6
    c1
    cuz
    cfv
    #
    @5
    vk
    csu
    #
    cr
    cn
    @15
    @5
    vk
    nnuz
    sumeq1i
    #
    @13
    c1
    cn
    wcel
    #
    @16
    cr
    wcel
    1nn
    vx
    @3
    vk
    vn
    cF
    c1
    rpnnen2.1
    rpnnen2lem6
    mpan2
    syl5eqel
    syl
    #
    @11
    @5
    vk
    @4
    c1
    cn
    nnuz
    @11
    1zzd
    #
    @11
    @2
    cn
    wcel
    #
    wa
    @5
    eqidd
    @11
    cn
    cr
    @2
    @4
    @11
    @13
    cn
    cr
    @4
    wf
    @14
    vx
    @3
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    syl
    ffvelrnda
    @11
    @13
    @18
    caddc
    @4
    c1
    cseq
    cli
    cdm
    wcel
    @14
    1nn
    vx
    @3
    vn
    cF
    c1
    rpnnen2.1
    rpnnen2lem5
    sylancl
    @11
    @13
    @21
    cc0
    @5
    cle
    wbr
    #
    @14
    @13
    @21
    wa
    @22
    @5
    @2
    cn
    cF
    cfv
    #
    cfv
    #
    cle
    wbr
    #
    @13
    cn
    cn
    wss
    #
    @21
    @22
    @25
    wa
    cn
    ssid
    #
    vx
    @3
    cn
    vk
    vn
    cF
    rpnnen2.1
    rpnnen2lem4
    mp3an2
    simpld
    sylan
    isumge0
    @11
    @6
    c1
    c2
    cdiv
    co
    #
    c1
    @19
    @28
    cr
    wcel
    @11
    halfre
    a1i
    c1
    cr
    wcel
    @11
    1re
    a1i
    @11
    @6
    @16
    @28
    cle
    @17
    @11
    @16
    @15
    @24
    vk
    csu
    #
    @28
    cle
    @11
    @13
    @16
    @29
    cle
    wbr
    #
    @14
    @13
    @26
    @18
    @30
    @27
    1nn
    vx
    @3
    cn
    vk
    vn
    cF
    c1
    rpnnen2.1
    rpnnen2lem7
    mp3an23
    syl
    @11
    @24
    @28
    vk
    @23
    c1
    @15
    @15
    eqid
    @20
    @11
    @2
    @15
    wcel
    #
    wa
    @24
    eqidd
    @31
    @24
    cc
    wcel
    #
    @11
    @31
    @21
    @32
    @2
    elnnuz
    @21
    @24
    cn
    cr
    @2
    @23
    @26
    cn
    cr
    @23
    wf
    @27
    vx
    cn
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    ax-mp
    ffvelrni
    recnd
    sylbir
    adantl
    caddc
    @23
    c1
    cseq
    @28
    cli
    wbr
    @11
    vx
    vn
    cF
    rpnnen2.1
    rpnnen2lem3
    a1i
    isumclim
    breqtrd
    syl5eqbr
    @28
    c1
    cle
    wbr
    @11
    @28
    c1
    halfre
    1re
    halflt1
    ltleii
    a1i
    letrd
    cc0
    c1
    @6
    0re
    1re
    elicc2i
    syl3anbrc
    @11
    @7
    @1
    wcel
    #
    wa
    #
    @6
    @10
    wceq
    #
    @3
    @7
    wceq
    #
    @34
    @35
    @3
    @7
    @34
    @3
    @7
    wne
    #
    vn
    cv
    #
    vm
    cv
    #
    clt
    wbr
    #
    @38
    @3
    wcel
    #
    @38
    @7
    wcel
    #
    wb
    #
    wi
    #
    vn
    cn
    wral
    #
    vm
    @3
    @7
    cdif
    #
    wrex
    #
    @45
    vm
    @7
    @3
    cdif
    #
    wrex
    #
    wo
    #
    @35
    wn
    #
    @34
    @37
    @45
    vm
    @46
    @48
    cun
    #
    wrex
    #
    @50
    @34
    @37
    @39
    @38
    cle
    wbr
    #
    vn
    @52
    wral
    #
    vm
    @52
    wrex
    #
    @53
    @34
    @37
    @56
    @34
    @52
    cn
    wss
    #
    @52
    c0
    wne
    #
    @56
    @37
    @11
    @13
    @7
    cn
    wss
    #
    @57
    @33
    @14
    @7
    cn
    elpwi
    #
    @13
    @46
    cn
    wss
    #
    @48
    cn
    wss
    #
    @57
    @59
    @3
    cn
    @7
    ssdifss
    @7
    cn
    @3
    ssdifss
    @61
    @62
    wa
    @57
    @46
    @48
    cn
    unss
    biimpi
    syl2an
    syl2an
    #
    @37
    @58
    @3
    @7
    @52
    c0
    @36
    @3
    @7
    wss
    #
    @7
    @3
    wss
    #
    wa
    @46
    c0
    wceq
    #
    @48
    c0
    wceq
    #
    wa
    @52
    c0
    wceq
    @3
    @7
    eqss
    @64
    @66
    @65
    @67
    @3
    @7
    ssdif0
    @7
    @3
    ssdif0
    anbi12i
    @46
    @48
    un00
    3bitri
    necon3bii
    biimpi
    vm
    vn
    @52
    nnwo
    syl2an
    ex
    @34
    @55
    @45
    vm
    @52
    @34
    @39
    @52
    wcel
    wa
    @39
    cn
    wcel
    #
    @55
    @45
    wi
    @34
    @52
    cn
    @39
    @63
    sselda
    @55
    @54
    wn
    #
    @43
    wi
    #
    vn
    wal
    #
    @68
    @45
    @55
    @38
    @52
    wcel
    #
    @54
    wi
    #
    vn
    wal
    @71
    @54
    vn
    @52
    df-ral
    @73
    @70
    vn
    @73
    @69
    @72
    wn
    #
    wi
    @70
    @72
    @54
    con34b
    @74
    @43
    @69
    @43
    @72
    @38
    @46
    wcel
    #
    @38
    @48
    wcel
    #
    wo
    @41
    @42
    wn
    wa
    #
    @42
    @41
    wn
    wa
    #
    wo
    @72
    @43
    wn
    @75
    @77
    @76
    @78
    @38
    @3
    @7
    eldif
    @38
    @7
    @3
    eldif
    orbi12i
    @38
    @46
    @48
    elun
    @41
    @42
    xor
    3bitr4ri
    con1bii
    imbi2i
    bitri
    albii
    bitri
    @71
    @45
    @68
    @70
    vn
    cn
    wral
    @70
    vn
    cn
    alral
    @68
    @44
    @70
    vn
    cn
    @68
    @38
    cn
    wcel
    #
    wa
    @40
    @69
    @43
    @79
    @38
    cr
    wcel
    @39
    cr
    wcel
    @40
    @69
    wb
    @68
    @38
    nnre
    @39
    nnre
    @38
    @39
    ltnle
    syl2anr
    imbi1d
    ralbidva
    syl5ibr
    syl5bi
    syl
    reximdva
    syld
    @45
    vm
    @46
    @48
    rexun
    syl6ib
    @11
    @13
    @59
    @50
    @51
    wi
    @33
    @14
    @60
    @13
    @59
    wa
    #
    @47
    @51
    @49
    @80
    @45
    @51
    vm
    @46
    @80
    @39
    @46
    wcel
    #
    @45
    wa
    #
    wa
    @35
    vx
    @3
    @7
    vk
    vm
    vn
    cF
    rpnnen2.1
    @13
    @59
    @82
    simpll
    @13
    @59
    @82
    simplr
    @80
    @81
    @45
    simprl
    @80
    @81
    @45
    simprr
    @35
    biid
    rpnnen2lem11
    rexlimdvaa
    @80
    @45
    @51
    vm
    @48
    @80
    @39
    @48
    wcel
    #
    @45
    wa
    #
    wa
    #
    @35
    vx
    @7
    @3
    vk
    vm
    vn
    cF
    rpnnen2.1
    @13
    @59
    @84
    simplr
    @13
    @59
    @84
    simpll
    @80
    @83
    @45
    simprl
    @85
    @45
    @40
    @42
    @41
    wb
    #
    wi
    #
    vn
    cn
    wral
    @80
    @83
    @45
    simprr
    @87
    @44
    vn
    cn
    @86
    @43
    @40
    @42
    @41
    bicom
    imbi2i
    ralbii
    sylibr
    @6
    @10
    eqcom
    rpnnen2lem11
    rexlimdvaa
    jaod
    syl2an
    syld
    necon4ad
    @36
    cn
    @5
    @9
    vk
    @36
    @2
    @4
    @8
    @3
    @7
    cF
    fveq2
    fveq1d
    sumeq2sdv
    impbid1
    dom2
    ax-mp
end
