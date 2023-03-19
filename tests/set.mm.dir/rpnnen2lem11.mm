include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "csu.mm"
include "wne.mm"
include "wn.mm"
include "cn.mm"
include "wss.mm"
include "wcel.mm"
include "cr.mm"
include "cdif.mm"
include "eldifi.mm"
include "ssel2.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "rpnnen2lem6.mm"
include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cn0.mm"
include "3nn.mm"
include "nnrecre.mm"
include "ax-mp.mm"
include "nnnn0d.mm"
include "reexpcl.mm"
include "sylancr.mm"
include "c2.mm"
include "crp.mm"
include "cz.mm"
include "nnrp.mm"
include "rpreccl.mm"
include "mp2b.mm"
include "nnzd.mm"
include "rpexpcl.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "csn.mm"
include "cle.mm"
include "wbr.mm"
include "snssd.mm"
include "ssdifd.mm"
include "sstrd.mm"
include "wb.mm"
include "ssconb.mm"
include "mpbird.mm"
include "difssd.mm"
include "rpnnen2lem7.mm"
include "syl3anc.mm"
include "cc0.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "rpnnen2lem9.mm"
include "syl.mm"
include "cmul.mm"
include "cc.mm"
include "recni.mm"
include "expp1.mm"
include "recnd.mm"
include "3cn.mm"
include "3ne0.mm"
include "divrec.mm"
include "mp3an23.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "wa.mm"
include "ax-1cn.mm"
include "pm3.2i.mm"
include "divsubdir.mm"
include "mp3an.mm"
include "3m1e2.mm"
include "oveq1i.mm"
include "dividi.mm"
include "3eqtr3ri.mm"
include "oveq2i.mm"
include "2cnne0.mm"
include "divcan7.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "clt.mm"
include "rphalflt.mm"
include "lelttrd.mm"
include "cif.mm"
include "eluznn.mm"
include "sylan.mm"
include "rpnnen2lem1.mm"
include "syldan.mm"
include "sumeq2dv.mm"
include "wral.mm"
include "cfn.mm"
include "wo.mm"
include "uzid.mm"
include "vex.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "ralsn.mm"
include "sylibr.mm"
include "ssid.mm"
include "a1i.mm"
include "orcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "sumsn.mm"
include "3eqtr2d.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "gtned.mm"
include "rpnnen2lem10.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem rpnnen2lem11
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )
  assume rpnnen2.2: |- ( ph -> A C_ NN )
  assume rpnnen2.3: |- ( ph -> B C_ NN )
  assume rpnnen2.4: |- ( ph -> m e. ( A \ B ) )
  assume rpnnen2.5: |- ( ph -> A. n e. NN ( n < m -> ( n e. A <-> n e. B ) ) )
  assume rpnnen2.6: |- ( ps <-> sum_ k e. NN ( ( F ` A ) ` k ) = sum_ k e. NN ( ( F ` B ) ` k ) )

  disjoint m n
  disjoint m x
  disjoint n x
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint F k
  disjoint F m
  disjoint k ph
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k y
  disjoint k z
  disjoint F y
  disjoint F z
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint N n
  assert |- ( ph -> -. ps )

  proof
    wph
    vm
    cv
    #
    cuz
    cfv
    #
    vk
    cv
    #
    cA
    cF
    cfv
    cfv
    vk
    csu
    #
    @1
    @2
    cB
    cF
    cfv
    cfv
    vk
    csu
    #
    wne
    wps
    wn
    wph
    @4
    @3
    wph
    cB
    cn
    wss
    #
    @0
    cn
    wcel
    #
    @4
    cr
    wcel
    rpnnen2.3
    wph
    cA
    cn
    wss
    #
    @0
    cA
    cB
    cdif
    #
    wcel
    #
    @6
    rpnnen2.2
    rpnnen2.4
    @9
    @7
    @0
    cA
    wcel
    #
    @6
    @0
    cA
    cB
    eldifi
    #
    cA
    cn
    @0
    ssel2
    sylan2
    syl2anc
    #
    vx
    cB
    vk
    vn
    cF
    @0
    rpnnen2.1
    rpnnen2lem6
    syl2anc
    #
    wph
    @4
    c1
    c3
    cdiv
    co
    #
    @0
    cexp
    co
    #
    @3
    @13
    wph
    @14
    cr
    wcel
    #
    @0
    cn0
    wcel
    #
    @15
    cr
    wcel
    c3
    cn
    wcel
    #
    @16
    3nn
    c3
    nnrecre
    ax-mp
    #
    wph
    @0
    @12
    nnnn0d
    #
    @14
    @0
    reexpcl
    sylancr
    wph
    @7
    @6
    @3
    cr
    wcel
    rpnnen2.2
    @12
    vx
    cA
    vk
    vn
    cF
    @0
    rpnnen2.1
    rpnnen2lem6
    syl2anc
    wph
    @4
    @15
    c2
    cdiv
    co
    #
    @15
    @13
    wph
    @15
    wph
    @15
    wph
    @14
    crp
    wcel
    #
    @0
    cz
    wcel
    #
    @15
    crp
    wcel
    #
    @18
    c3
    crp
    wcel
    @22
    3nn
    c3
    nnrp
    c3
    rpreccl
    mp2b
    wph
    @0
    @12
    nnzd
    #
    @14
    @0
    rpexpcl
    sylancr
    #
    rpred
    #
    rehalfcld
    #
    @27
    wph
    @4
    @1
    @2
    cn
    @0
    csn
    #
    cdif
    #
    cF
    cfv
    cfv
    vk
    csu
    #
    @21
    cle
    wph
    cB
    @30
    wss
    #
    @30
    cn
    wss
    @6
    @4
    @31
    cle
    wbr
    wph
    @32
    @29
    cn
    cB
    cdif
    #
    wss
    #
    wph
    @29
    @8
    @33
    wph
    @0
    @8
    rpnnen2.4
    snssd
    wph
    cA
    cn
    cB
    rpnnen2.2
    ssdifd
    sstrd
    wph
    @5
    @29
    cn
    wss
    #
    @32
    @34
    wb
    rpnnen2.3
    wph
    @0
    cn
    @12
    snssd
    #
    cB
    @29
    cn
    ssconb
    syl2anc
    mpbird
    wph
    cn
    @29
    difssd
    @12
    vx
    cB
    @30
    vk
    vn
    cF
    @0
    rpnnen2.1
    rpnnen2lem7
    syl3anc
    wph
    @31
    cc0
    @14
    @0
    c1
    caddc
    co
    cexp
    co
    #
    c1
    @14
    cmin
    co
    #
    cdiv
    co
    #
    caddc
    co
    #
    cc0
    @21
    caddc
    co
    @21
    wph
    @6
    @31
    @40
    wceq
    @12
    vx
    vk
    vn
    cF
    @0
    rpnnen2.1
    rpnnen2lem9
    syl
    wph
    @39
    @21
    cc0
    caddc
    wph
    @39
    @15
    c3
    cdiv
    co
    #
    @38
    cdiv
    co
    #
    @21
    wph
    @37
    @41
    @38
    cdiv
    wph
    @37
    @15
    @14
    cmul
    co
    #
    @41
    wph
    @14
    cc
    wcel
    @17
    @37
    @43
    wceq
    @14
    @19
    recni
    @20
    @14
    @0
    expp1
    sylancr
    wph
    @15
    cc
    wcel
    #
    @41
    @43
    wceq
    #
    wph
    @15
    @27
    recnd
    #
    @44
    c3
    cc
    wcel
    #
    c3
    cc0
    wne
    #
    @45
    3cn
    3ne0
    @15
    c3
    divrec
    mp3an23
    syl
    eqtr4d
    oveq1d
    wph
    @42
    @41
    c2
    c3
    cdiv
    co
    #
    cdiv
    co
    #
    @21
    @38
    @49
    @41
    cdiv
    c3
    c1
    cmin
    co
    #
    c3
    cdiv
    co
    #
    c3
    c3
    cdiv
    co
    #
    @14
    cmin
    co
    #
    @49
    @38
    @47
    c1
    cc
    wcel
    @47
    @48
    wa
    #
    @52
    @54
    wceq
    3cn
    ax-1cn
    @47
    @48
    3cn
    3ne0
    pm3.2i
    #
    c3
    c1
    c3
    divsubdir
    mp3an
    @51
    c2
    c3
    cdiv
    3m1e2
    oveq1i
    @53
    c1
    @14
    cmin
    c3
    3cn
    3ne0
    dividi
    oveq1i
    3eqtr3ri
    oveq2i
    wph
    @44
    @50
    @21
    wceq
    #
    @46
    @44
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @55
    @57
    2cnne0
    @56
    @15
    c2
    c3
    divcan7
    mp3an23
    syl
    syl5eq
    eqtrd
    oveq2d
    wph
    @21
    wph
    @21
    @28
    recnd
    addid2d
    3eqtrd
    breqtrd
    wph
    @24
    @21
    @15
    clt
    wbr
    @26
    @15
    rphalflt
    syl
    lelttrd
    wph
    @1
    @2
    @29
    cF
    cfv
    cfv
    #
    vk
    csu
    #
    @15
    @3
    cle
    wph
    @59
    @1
    @2
    @29
    wcel
    @14
    @2
    cexp
    co
    #
    cc0
    cif
    #
    vk
    csu
    #
    @29
    @60
    vk
    csu
    #
    @15
    wph
    @1
    @58
    @61
    vk
    wph
    @2
    @1
    wcel
    #
    @2
    cn
    wcel
    #
    @58
    @61
    wceq
    #
    wph
    @6
    @64
    @65
    @12
    @2
    @0
    eluznn
    sylan
    wph
    @35
    @65
    @66
    @36
    vx
    @29
    vn
    cF
    @2
    rpnnen2.1
    rpnnen2lem1
    sylan
    syldan
    sumeq2dv
    wph
    @29
    @1
    wss
    @60
    cc
    wcel
    #
    vk
    @29
    wral
    #
    @1
    @1
    wss
    #
    @1
    cfn
    wcel
    #
    wo
    @63
    @62
    wceq
    wph
    @0
    @1
    wph
    @23
    @0
    @1
    wcel
    @25
    @0
    uzid
    syl
    snssd
    wph
    @44
    @68
    @46
    @67
    @44
    vk
    @0
    vm
    vex
    @2
    @0
    wceq
    @60
    @15
    cc
    @2
    @0
    @14
    cexp
    oveq2
    #
    eleq1d
    ralsn
    sylibr
    wph
    @69
    @70
    @69
    wph
    @1
    ssid
    a1i
    orcd
    @29
    @1
    @60
    vk
    @0
    sumss2
    syl21anc
    wph
    @6
    @44
    @63
    @15
    wceq
    @12
    @46
    @60
    @15
    vk
    @0
    cn
    @71
    sumsn
    syl2anc
    3eqtr2d
    wph
    @29
    cA
    wss
    @7
    @6
    @59
    @3
    cle
    wbr
    wph
    @0
    cA
    wph
    @9
    @10
    rpnnen2.4
    @11
    syl
    snssd
    rpnnen2.2
    @12
    vx
    @29
    cA
    vk
    vn
    cF
    @0
    rpnnen2.1
    rpnnen2lem7
    syl3anc
    eqbrtrrd
    ltletrd
    gtned
    wph
    wps
    @3
    @4
    wph
    wps
    @3
    @4
    wceq
    wph
    wps
    vx
    cA
    cB
    vk
    vm
    vn
    cF
    rpnnen2.1
    rpnnen2.2
    rpnnen2.3
    rpnnen2.4
    rpnnen2.5
    rpnnen2.6
    rpnnen2lem10
    ex
    necon3ad
    mpd
end
