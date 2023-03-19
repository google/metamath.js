include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "resubcld.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "rpred.mm"
include "remulcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "negsubdi2d.mm"
include "c1.mm"
include "1red.mm"
include "remulcld.mm"
include "cv.mm"
include "c4.mm"
include "c3.mm"
include "cdiv.mm"
include "caddc.mm"
include "3re.mm"
include "3ne0.mm"
include "rereccli.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "4re.mm"
include "3pm3.2i.mm"
include "redivcl.mm"
include "mp1i.mm"
include "lesub1dd.mm"
include "ltsub2dd.mm"
include "lelttrd.mm"
include "subcld.mm"
include "subdird.mm"
include "sub4d.mm"
include "subsub2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "subidd.mm"
include "4cn.mm"
include "3cn.mm"
include "divcli.mm"
include "ax-1cn.mm"
include "1div1e1.mm"
include "oveq2i.mm"
include "ax-1ne0.mm"
include "divadddivi.mm"
include "eqtr3i.mm"
include "addcomi.mm"
include "df-4.mm"
include "1t1e1.mm"
include "mulid2i.mm"
include "oveq12i.mm"
include "3eqtr4ri.mm"
include "oveq1i.mm"
include "3t1e3.mm"
include "3eqtri.mm"
include "subaddrii.mm"
include "1e0p1.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "1lt2.mm"
include "ltmul1d.mm"
include "mpbii.mm"
include "lttrd.mm"
include "eqbrtrd.mm"
include "ltnegcon1d.mm"
include "c5.mm"
include "5re.mm"
include "redivcld.mm"
include "renegcld.mm"
include "readdcld.mm"
include "ltnegd.mm"
include "mpbid.mm"
include "lt2addd.mm"
include "negsubd.mm"
include "adddird.mm"
include "eqcomd.mm"
include "negcld.mm"
include "mulneg1d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "negeqd.mm"
include "mulcld.mm"
include "negdid.mm"
include "negnegd.mm"
include "oveq12d.mm"
include "add4d.mm"
include "negidd.mm"
include "addcld.mm"
include "addid2d.mm"
include "adddid.mm"
include "divcan2i.mm"
include "df-5.mm"
include "3eqtr4i.mm"
include "mvllmuld.mm"
include "3eqtr2d.mm"
include "3brtr3d.mm"
include "c6.mm"
include "5lt6.mm"
include "3t2e6.mm"
include "breqtrri.mm"
include "wa.mm"
include "wb.mm"
include "3pos.mm"
include "pm3.2i.mm"
include "ltdivmul.mm"
include "mp3an.mm"
include "mpbir.mm"
include "ltmul1dd.mm"
include "absltd.mm"
include "mpbir2and.mm"

theorem stoweidlem13
  let wph: wff ph
  let vj: setvar j
  let cE: class E
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem13.1: |- ( ph -> E e. RR+ )
  assume stoweidlem13.2: |- ( ph -> X e. RR )
  assume stoweidlem13.3: |- ( ph -> Y e. RR )
  assume stoweidlem13.4: |- ( ph -> j e. RR )
  assume stoweidlem13.5: |- ( ph -> ( ( j - ( 4 / 3 ) ) x. E ) < X )
  assume stoweidlem13.6: |- ( ph -> X <_ ( ( j - ( 1 / 3 ) ) x. E ) )
  assume stoweidlem13.7: |- ( ph -> ( ( j - ( 4 / 3 ) ) x. E ) < Y )
  assume stoweidlem13.8: |- ( ph -> Y < ( ( j + ( 1 / 3 ) ) x. E ) )


  assert |- ( ph -> ( abs ` ( Y - X ) ) < ( 2 x. E ) )

  proof
    wph
    cY
    cX
    cmin
    co
    #
    cabs
    cfv
    c2
    cE
    cmul
    co
    #
    clt
    wbr
    @1
    cneg
    @0
    clt
    wbr
    @0
    @1
    clt
    wbr
    wph
    @0
    @1
    wph
    cY
    cX
    stoweidlem13.3
    stoweidlem13.2
    resubcld
    #
    wph
    c2
    cr
    wcel
    #
    cE
    cr
    wcel
    @1
    cr
    wcel
    2re
    wph
    cE
    stoweidlem13.1
    rpred
    #
    c2
    cE
    remulcl
    sylancr
    #
    wph
    @0
    cneg
    cX
    cY
    cmin
    co
    #
    @1
    clt
    wph
    cY
    cX
    wph
    cY
    stoweidlem13.3
    recnd
    #
    wph
    cX
    stoweidlem13.2
    recnd
    #
    negsubdi2d
    wph
    @6
    c1
    cE
    cmul
    co
    #
    @1
    wph
    cX
    cY
    stoweidlem13.2
    stoweidlem13.3
    resubcld
    #
    wph
    c1
    cE
    wph
    1red
    #
    @4
    remulcld
    @5
    wph
    @6
    vj
    cv
    #
    @12
    cmin
    co
    #
    c4
    c3
    cdiv
    co
    #
    c1
    c3
    cdiv
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    cE
    cmul
    co
    #
    @9
    clt
    wph
    @6
    @12
    @15
    cmin
    co
    #
    cE
    cmul
    co
    #
    @12
    @14
    cmin
    co
    #
    cE
    cmul
    co
    #
    cmin
    co
    #
    @18
    clt
    wph
    @6
    @20
    cY
    cmin
    co
    @23
    @10
    wph
    @20
    cY
    wph
    @19
    cE
    wph
    @12
    @15
    stoweidlem13.4
    @15
    cr
    wcel
    wph
    c3
    3re
    3ne0
    rereccli
    a1i
    #
    resubcld
    @4
    remulcld
    #
    stoweidlem13.3
    resubcld
    wph
    @20
    @22
    @25
    wph
    @21
    cE
    wph
    @12
    @14
    stoweidlem13.4
    c4
    cr
    wcel
    #
    c3
    cr
    wcel
    #
    c3
    cc0
    wne
    #
    w3a
    @14
    cr
    wcel
    wph
    @26
    @27
    @28
    4re
    3re
    3ne0
    3pm3.2i
    c4
    c3
    redivcl
    mp1i
    #
    resubcld
    @4
    remulcld
    #
    resubcld
    wph
    cX
    @20
    cY
    stoweidlem13.2
    @25
    stoweidlem13.3
    stoweidlem13.6
    lesub1dd
    wph
    @22
    cY
    @20
    @30
    stoweidlem13.3
    @25
    stoweidlem13.7
    ltsub2dd
    lelttrd
    wph
    @19
    @21
    cmin
    co
    #
    cE
    cmul
    co
    @23
    @18
    wph
    @19
    @21
    cE
    wph
    @12
    @15
    wph
    @12
    stoweidlem13.4
    recnd
    #
    wph
    @15
    @24
    recnd
    #
    subcld
    wph
    @12
    @14
    @32
    wph
    @14
    @29
    recnd
    #
    subcld
    wph
    cE
    @4
    recnd
    #
    subdird
    wph
    @31
    @17
    cE
    cmul
    wph
    @31
    @13
    @15
    @14
    cmin
    co
    cmin
    co
    @17
    wph
    @12
    @15
    @12
    @14
    @32
    @33
    @32
    @34
    sub4d
    wph
    @13
    @15
    @14
    wph
    @12
    @12
    @32
    @32
    subcld
    @33
    @34
    subsub2d
    eqtrd
    oveq1d
    eqtr3d
    breqtrd
    wph
    @17
    c1
    cE
    cmul
    wph
    @17
    cc0
    @16
    caddc
    co
    #
    c1
    wph
    @13
    cc0
    @16
    caddc
    wph
    @12
    @32
    subidd
    oveq1d
    @36
    cc0
    c1
    caddc
    co
    c1
    @16
    c1
    cc0
    caddc
    @14
    @15
    c1
    c4
    c3
    4cn
    3cn
    3ne0
    divcli
    c1
    c3
    ax-1cn
    3cn
    3ne0
    divcli
    ax-1cn
    @15
    c1
    caddc
    co
    #
    c1
    c1
    cmul
    co
    #
    c1
    c3
    cmul
    co
    #
    caddc
    co
    #
    c3
    c1
    cmul
    co
    #
    cdiv
    co
    #
    c4
    @41
    cdiv
    co
    @14
    @15
    c1
    c1
    cdiv
    co
    #
    caddc
    co
    @37
    @42
    @43
    c1
    @15
    caddc
    1div1e1
    oveq2i
    c1
    c3
    c1
    c1
    ax-1cn
    3cn
    ax-1cn
    ax-1cn
    3ne0
    ax-1ne0
    divadddivi
    eqtr3i
    @40
    c4
    @41
    cdiv
    c3
    c1
    caddc
    co
    c1
    c3
    caddc
    co
    c4
    @40
    c3
    c1
    3cn
    ax-1cn
    addcomi
    df-4
    @38
    c1
    @39
    c3
    caddc
    1t1e1
    c3
    3cn
    mulid2i
    oveq12i
    3eqtr4ri
    oveq1i
    @41
    c3
    c4
    cdiv
    3t1e3
    oveq2i
    3eqtri
    subaddrii
    oveq2i
    1e0p1
    eqtr4i
    syl6eq
    oveq1d
    breqtrd
    wph
    c1
    c2
    clt
    wbr
    @9
    @1
    clt
    wbr
    1lt2
    wph
    c1
    c2
    cE
    @11
    @3
    wph
    2re
    a1i
    #
    stoweidlem13.1
    ltmul1d
    mpbii
    lttrd
    eqbrtrd
    ltnegcon1d
    wph
    @0
    c5
    c3
    cdiv
    co
    #
    cE
    cmul
    co
    #
    @1
    @2
    wph
    @45
    cE
    wph
    c5
    c3
    c5
    cr
    wcel
    #
    wph
    5re
    a1i
    @27
    wph
    3re
    a1i
    #
    @28
    wph
    3ne0
    a1i
    #
    redivcld
    #
    @4
    remulcld
    @5
    wph
    cY
    cX
    cneg
    #
    caddc
    co
    @12
    @15
    caddc
    co
    #
    cE
    cmul
    co
    #
    @22
    cneg
    #
    caddc
    co
    #
    @0
    @46
    clt
    wph
    cY
    @51
    @53
    @54
    stoweidlem13.3
    wph
    cX
    stoweidlem13.2
    renegcld
    wph
    @52
    cE
    wph
    @12
    @15
    stoweidlem13.4
    @24
    readdcld
    @4
    remulcld
    wph
    @22
    @30
    renegcld
    stoweidlem13.8
    wph
    @22
    cX
    clt
    wbr
    @51
    @54
    clt
    wbr
    stoweidlem13.5
    wph
    @22
    cX
    @30
    stoweidlem13.2
    ltnegd
    mpbid
    lt2addd
    wph
    cY
    cX
    @7
    @8
    negsubd
    wph
    @55
    @12
    cE
    cmul
    co
    #
    @15
    cE
    cmul
    co
    #
    caddc
    co
    #
    @56
    cneg
    #
    @14
    cE
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @46
    wph
    @53
    @58
    @54
    @61
    caddc
    wph
    @12
    @15
    cE
    @32
    @33
    @35
    adddird
    wph
    @54
    @56
    @60
    cneg
    #
    caddc
    co
    #
    cneg
    @59
    @63
    cneg
    #
    caddc
    co
    @61
    wph
    @22
    @64
    wph
    @22
    @12
    @14
    cneg
    #
    caddc
    co
    #
    cE
    cmul
    co
    @56
    @66
    cE
    cmul
    co
    #
    caddc
    co
    @64
    wph
    @21
    @67
    cE
    cmul
    wph
    @67
    @21
    wph
    @12
    @14
    @32
    @34
    negsubd
    eqcomd
    oveq1d
    wph
    @12
    @66
    cE
    @32
    wph
    @14
    @34
    negcld
    @35
    adddird
    wph
    @68
    @63
    @56
    caddc
    wph
    @14
    cE
    @34
    @35
    mulneg1d
    oveq2d
    3eqtrd
    negeqd
    wph
    @56
    @63
    wph
    @12
    cE
    @32
    @35
    mulcld
    #
    wph
    @60
    wph
    @14
    cE
    @34
    @35
    mulcld
    #
    negcld
    negdid
    wph
    @65
    @60
    @59
    caddc
    wph
    @60
    @70
    negnegd
    oveq2d
    3eqtrd
    oveq12d
    wph
    @62
    @57
    @60
    caddc
    co
    #
    @15
    @14
    caddc
    co
    #
    cE
    cmul
    co
    @46
    wph
    @62
    @56
    @59
    caddc
    co
    #
    @71
    caddc
    co
    cc0
    @71
    caddc
    co
    @71
    wph
    @56
    @57
    @59
    @60
    @69
    wph
    @15
    cE
    @33
    @35
    mulcld
    #
    wph
    @56
    @69
    negcld
    @70
    add4d
    wph
    @73
    cc0
    @71
    caddc
    wph
    @56
    @69
    negidd
    oveq1d
    wph
    @71
    wph
    @57
    @60
    @74
    @70
    addcld
    addid2d
    3eqtrd
    wph
    @15
    @14
    cE
    @33
    @34
    @35
    adddird
    wph
    @72
    @45
    cE
    cmul
    wph
    c3
    @72
    c5
    wph
    c3
    @48
    recnd
    #
    wph
    @15
    @14
    @33
    @34
    addcld
    @49
    wph
    c3
    @72
    cmul
    co
    c3
    @15
    cmul
    co
    #
    c3
    @14
    cmul
    co
    #
    caddc
    co
    #
    c5
    wph
    c3
    @15
    @14
    @75
    @33
    @34
    adddid
    c1
    c4
    caddc
    co
    c4
    c1
    caddc
    co
    @78
    c5
    c1
    c4
    ax-1cn
    4cn
    addcomi
    @76
    c1
    @77
    c4
    caddc
    c1
    c3
    ax-1cn
    3cn
    3ne0
    divcan2i
    c4
    c3
    4cn
    3cn
    3ne0
    divcan2i
    oveq12i
    df-5
    3eqtr4i
    syl6eq
    mvllmuld
    oveq1d
    3eqtr2d
    eqtrd
    3brtr3d
    wph
    @45
    c2
    cE
    @50
    @44
    stoweidlem13.1
    @45
    c2
    clt
    wbr
    #
    wph
    @79
    c5
    c3
    c2
    cmul
    co
    #
    clt
    wbr
    #
    c5
    c6
    @80
    clt
    5lt6
    3t2e6
    breqtrri
    @47
    @3
    @27
    cc0
    c3
    clt
    wbr
    #
    wa
    @79
    @81
    wb
    5re
    2re
    @27
    @82
    3re
    3pos
    pm3.2i
    c5
    c2
    c3
    ltdivmul
    mp3an
    mpbir
    a1i
    ltmul1dd
    lttrd
    wph
    @0
    @1
    @2
    @5
    absltd
    mpbir2and
end
